import JuliaLean.Base64Uuid.HexProofs
import JuliaLean.Base64Uuid.Props

/-!
`UUID(string(u)) == u`: `string` writes the 32 nibbles of `u.value` as lowercase hex
digits around four dashes, and `parseuuid` reads them back eight digits at a time with
`Parsers.ishexdigits8` and `Parsers.hexdigits8` (see `HexProofs`).
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- The value `string(::UUID)` holds after `k` shifts, `u >> 4k`. -/
def sh : Nat → U128 → U128
  | 0, v => v
  | k + 1, v => shr (sh k v) 4

/-- The digit `string(::UUID)` stores for the current value, `hex_chars[1 + u & 0xf]`. -/
def nib (v : U128) : Byte := hex_chars.getD (bn (JInt.rem .u8 (band v (JInt.lit .u128 0xf)))) (b8 0)

/-- `string(::UUID)` with the digit function `g` and the shift `s` left abstract. -/
def strG {α : Type} (g : α → Byte) (s : α → α) (v : α) : List Byte :=
  let (a, _) := groupings.foldl
    (fun (acc : List Byte × α) (i : Nat) =>
      let (a, v) := acc
      (a.set (i - 1) (g v), s v))
    (List.replicate 36 (b8 0), v)
  ((((a.set 8 (b8 45)).set 13 (b8 45)).set 18 (b8 45)).set 23 (b8 45))

theorem uuidString_strG (u : UUID) : uuidString u =
    strG (fun v => hex_chars.getD (bn (JInt.rem .u8 (band v (JInt.lit .u128 0xf)))) (b8 0)) (fun v => shr v 4) u.value :=
  rfl

theorem set_cons_lit {α : Type} (a : α) (l : List α) (n : Nat) (b : α) (h : n ≠ 0) :
    (a :: l).set n b = a :: l.set (n - 1) b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem replicate_lit {α : Type} (n : Nat) (a : α) (h : n ≠ 0) : List.replicate n a = a :: List.replicate (n - 1) a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

theorem groupings_eq : groupings = [36, 35, 34, 33, 32, 31, 30, 29, 28, 27, 26, 25, 23, 22, 21, 20, 18, 17, 16, 15, 13, 12, 11, 10, 8, 7, 6, 5, 4, 3, 2, 1] := by decide

theorem strG_eq {α : Type} (g : α → Byte) (s : α → α) (v : α) : strG g s v =
    [g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))))))))))))), b8 45, g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))))))))), b8 45, g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))))), b8 45, g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))))), g (s (s (s (s (s (s (s (s (s (s (s (s (v))))))))))))), b8 45, g (s (s (s (s (s (s (s (s (s (s (s (v)))))))))))), g (s (s (s (s (s (s (s (s (s (s (v))))))))))), g (s (s (s (s (s (s (s (s (s (v)))))))))), g (s (s (s (s (s (s (s (s (v))))))))), g (s (s (s (s (s (s (s (v)))))))), g (s (s (s (s (s (s (v))))))), g (s (s (s (s (s (v)))))), g (s (s (s (s (v))))), g (s (s (s (v)))), g (s (s (v))), g (s (v)), g (v)] := by
  simp only [strG, groupings_eq, List.foldl_cons, List.foldl_nil]
  simp (disch := decide) only [replicate_lit, List.replicate_zero, set_cons_lit, List.set_cons_zero,
    Nat.reduceSub]

theorem uuidString_eq (u : UUID) : uuidString u =
    [nib (sh 31 u.value), nib (sh 30 u.value), nib (sh 29 u.value), nib (sh 28 u.value), nib (sh 27 u.value), nib (sh 26 u.value), nib (sh 25 u.value), nib (sh 24 u.value), b8 45, nib (sh 23 u.value), nib (sh 22 u.value), nib (sh 21 u.value), nib (sh 20 u.value), b8 45, nib (sh 19 u.value), nib (sh 18 u.value), nib (sh 17 u.value), nib (sh 16 u.value), b8 45, nib (sh 15 u.value), nib (sh 14 u.value), nib (sh 13 u.value), nib (sh 12 u.value), b8 45, nib (sh 11 u.value), nib (sh 10 u.value), nib (sh 9 u.value), nib (sh 8 u.value), nib (sh 7 u.value), nib (sh 6 u.value), nib (sh 5 u.value), nib (sh 4 u.value), nib (sh 3 u.value), nib (sh 2 u.value), nib (sh 1 u.value), nib (sh 0 u.value)] := by
  rw [uuidString_strG, strG_eq]
  rfl

theorem hexchar_get : ∀ d, d < 16 → hex_chars.getD d (b8 0) = b8 (hexc d) := by decide

theorem nib_eq (v : U128) : nib v = b8 (hexc (vn v % 16)) := by
  have h1 : bn (JInt.rem .u8 (band v (JInt.lit .u128 0xf))) = vn v % 16 := by
    rw [bn_eq_vn, vn_rem uns_u128 uns_u8, vn_band uns_u128, show vn (JInt.lit .u128 0xf) = 15 by decide,
      show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [IntTy.bits]
    all_goals omega
  unfold nib
  rw [h1]
  exact hexchar_get _ (Nat.mod_lt _ (by decide))

theorem vn_b8 (n : Nat) (h : n < 256) : vn (b8 n) = n := by
  unfold b8 JInt.lit
  rw [vn_wrap uns_u8]
  exact Nat.mod_eq_of_lt h

theorem sh_succ (k : Nat) (v : U128) : vn (sh (k + 1) v) = vn (sh k v) / 16 := by
  show vn (shr (sh k v) 4) = _
  rw [vn_shr uns_u128]

/-! ### `takebytes` -/

theorem go_spec : ∀ (l y : List Byte) (k : Nat) (w : JInt .u64), vn w < 2 ^ (8 * k) → k + l.length ≤ 8 →
    ∃ W, takebytes.go l.length k w (l ++ y) = (W, y, true) ∧ vn W = vn w + 2 ^ (8 * k) * lk 8 (l.map vn)
  | [], y, k, w, _, _ => ⟨w, rfl, by simp [lk]⟩
  | b :: l, y, k, w, hw, hk => by
    have hb : vn b < 2 ^ 8 := vn_lt uns_u8 b
    have hpk : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 2 ^ 8 := by rw [Nat.mul_succ, Nat.pow_add]
    have hle : 2 ^ (8 * (k + 1)) ≤ 2 ^ IntTy.u64.bits :=
      Nat.pow_le_pow_right (by decide) (by simp only [List.length_cons] at hk; simp only [IntTy.bits]; omega)
    have hlt : vn b * 2 ^ (8 * k) < 2 ^ IntTy.u64.bits := by
      have := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos (8 * k))
      rw [Nat.mul_comm (2 ^ 8), ← hpk] at this
      omega
    have hb64 : vn b < 2 ^ IntTy.u64.bits := Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by decide))
    have hw' : vn (bor w (shl (JInt.rem .u64 b) (8 * k))) = vn w + 2 ^ (8 * k) * vn b := by
      rw [vn_bor uns_u64, vn_shl uns_u64, vn_rem uns_u8 uns_u64, Nat.mod_eq_of_lt hb64, Nat.mod_eq_of_lt hlt,
        Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hw, Nat.add_comm]
    have hbnd : vn w + 2 ^ (8 * k) * vn b < 2 ^ (8 * (k + 1)) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * k)) (show vn b + 1 ≤ 2 ^ 8 from hb)
      rw [Nat.mul_succ] at this
      rw [hpk]
      omega
    obtain ⟨W, hW, hv⟩ := go_spec l y (k + 1) _ (hw' ▸ hbnd) (by simp only [List.length_cons] at hk; omega)
    refine ⟨W, hW, ?_⟩
    rw [hv, hw', hpk]
    simp only [List.map_cons, lk, Nat.mul_add, Nat.mul_assoc]
    omega

theorem take_lanes (l y : List Byte) (hl : l.length ≤ 8) :
    ∃ W, takebytes.go l.length 0 (JInt.lit .u64 0) (l ++ y) = (W, y, true) ∧ vn W = lk 8 (l.map vn) := by
  obtain ⟨W, h1, h2⟩ := go_spec l y 0 (JInt.lit .u64 0) (by decide) (by omega)
  refine ⟨W, h1, ?_⟩
  rw [h2, show vn (JInt.lit .u64 0) = 0 by decide]
  simp

/-! ### Words of the parsed string -/

theorem or_shift (X Z n N : Nat) (hX : X < 2 ^ n) (hZ : Z * 2 ^ n < 2 ^ N) :
    (Z * 2 ^ n % 2 ^ N) ||| X = X + 2 ^ n * Z := by
  rw [Nat.mod_eq_of_lt hZ, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hX, Nat.add_comm]

theorem w_lanes (b c : JInt .u64) (x1 x2 x3 x4 y1 y2 y3 y4 : Nat) (h1 : x1 < 256) (h2 : x2 < 256)
    (h3 : x3 < 256) (h4 : x4 < 256) (g1 : y1 < 256) (g2 : y2 < 256) (g3 : y3 < 256) (g4 : y4 < 256)
    (hb : vn b = lk 8 [45, x1, x2, x3, x4]) (hc : vn c = lk 8 [45, y1, y2, y3, y4]) :
    vn (bor (shr b 8) (shl (shr c 8) 32)) = lk 8 [x1, x2, x3, x4, y1, y2, y3, y4] := by
  rw [vn_bor uns_u64, vn_shr uns_u64, vn_shl uns_u64, vn_shr uns_u64, hb, hc, Nat.or_comm,
    or_shift _ _ 32 _ (by simp only [lk]; omega) (by simp only [lk, IntTy.bits]; omega)]
  simp only [lk]
  omega

theorem dash_lane (b : JInt .u64) (x1 x2 x3 x4 : Nat) (hb : vn b = lk 8 [45, x1, x2, x3, x4]) :
    vn (band b (JInt.lit .u64 0xff)) = 45 := by
  rw [vn_band uns_u64, hb, show vn (JInt.lit .u64 0xff) = 255 by decide,
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [lk]
  omega

/-- The bytes `string(::UUID)` writes for the nibbles `D 31, ..., D 0`. -/
def H (D : Nat → Nat) (k : Nat) : Byte := b8 (hexc (D k))

/-- `UInt8('-')`. -/
def dash : Byte := b8 45

def uuidBytes (D : Nat → Nat) : List Byte :=
  [H D 31, H D 30, H D 29, H D 28, H D 27, H D 26, H D 25, H D 24, dash, H D 23, H D 22, H D 21, H D 20, dash, H D 19, H D 18, H D 17, H D 16, dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0]

theorem vnH (D : Nat → Nat) (k : Nat) (h : D k < 16) : vn (H D k) = hexc (D k) :=
  vn_b8 _ (by have := (hex_facts _ h).1; omega)

theorem hexc_lt (d : Nat) (h : d < 16) : hexc d < 256 := by have := (hex_facts _ h).1; omega

theorem parse_uuidBytes (D : Nat → Nat) (hD : ∀ k, k < 32 → D k < 16) :
    ∃ U, parseuuid (uuidBytes D) = some U ∧
      vn U.value = (((((((((((((((((((((((((((((((D 31) * 16 + D 30) * 16 + D 29) * 16 + D 28) * 16 + D 27) * 16 + D 26) * 16 + D 25) * 16 + D 24) * 16 + D 23) * 16 + D 22) * 16 + D 21) * 16 + D 20) * 16 + D 19) * 16 + D 18) * 16 + D 17) * 16 + D 16) * 16 + D 15) * 16 + D 14) * 16 + D 13) * 16 + D 12) * 16 + D 11) * 16 + D 10) * 16 + D 9) * 16 + D 8) * 16 + D 7) * 16 + D 6) * 16 + D 5) * 16 + D 4) * 16 + D 3) * 16 + D 2) * 16 + D 1) * 16 + D 0 := by
  have d0 : D 0 < 16 := hD 0 (by decide)
  have c0 : hexc (D 0) < 256 := hexc_lt _ d0
  have d1 : D 1 < 16 := hD 1 (by decide)
  have c1 : hexc (D 1) < 256 := hexc_lt _ d1
  have d2 : D 2 < 16 := hD 2 (by decide)
  have c2 : hexc (D 2) < 256 := hexc_lt _ d2
  have d3 : D 3 < 16 := hD 3 (by decide)
  have c3 : hexc (D 3) < 256 := hexc_lt _ d3
  have d4 : D 4 < 16 := hD 4 (by decide)
  have c4 : hexc (D 4) < 256 := hexc_lt _ d4
  have d5 : D 5 < 16 := hD 5 (by decide)
  have c5 : hexc (D 5) < 256 := hexc_lt _ d5
  have d6 : D 6 < 16 := hD 6 (by decide)
  have c6 : hexc (D 6) < 256 := hexc_lt _ d6
  have d7 : D 7 < 16 := hD 7 (by decide)
  have c7 : hexc (D 7) < 256 := hexc_lt _ d7
  have d8 : D 8 < 16 := hD 8 (by decide)
  have c8 : hexc (D 8) < 256 := hexc_lt _ d8
  have d9 : D 9 < 16 := hD 9 (by decide)
  have c9 : hexc (D 9) < 256 := hexc_lt _ d9
  have d10 : D 10 < 16 := hD 10 (by decide)
  have c10 : hexc (D 10) < 256 := hexc_lt _ d10
  have d11 : D 11 < 16 := hD 11 (by decide)
  have c11 : hexc (D 11) < 256 := hexc_lt _ d11
  have d12 : D 12 < 16 := hD 12 (by decide)
  have c12 : hexc (D 12) < 256 := hexc_lt _ d12
  have d13 : D 13 < 16 := hD 13 (by decide)
  have c13 : hexc (D 13) < 256 := hexc_lt _ d13
  have d14 : D 14 < 16 := hD 14 (by decide)
  have c14 : hexc (D 14) < 256 := hexc_lt _ d14
  have d15 : D 15 < 16 := hD 15 (by decide)
  have c15 : hexc (D 15) < 256 := hexc_lt _ d15
  have d16 : D 16 < 16 := hD 16 (by decide)
  have c16 : hexc (D 16) < 256 := hexc_lt _ d16
  have d17 : D 17 < 16 := hD 17 (by decide)
  have c17 : hexc (D 17) < 256 := hexc_lt _ d17
  have d18 : D 18 < 16 := hD 18 (by decide)
  have c18 : hexc (D 18) < 256 := hexc_lt _ d18
  have d19 : D 19 < 16 := hD 19 (by decide)
  have c19 : hexc (D 19) < 256 := hexc_lt _ d19
  have d20 : D 20 < 16 := hD 20 (by decide)
  have c20 : hexc (D 20) < 256 := hexc_lt _ d20
  have d21 : D 21 < 16 := hD 21 (by decide)
  have c21 : hexc (D 21) < 256 := hexc_lt _ d21
  have d22 : D 22 < 16 := hD 22 (by decide)
  have c22 : hexc (D 22) < 256 := hexc_lt _ d22
  have d23 : D 23 < 16 := hD 23 (by decide)
  have c23 : hexc (D 23) < 256 := hexc_lt _ d23
  have d24 : D 24 < 16 := hD 24 (by decide)
  have c24 : hexc (D 24) < 256 := hexc_lt _ d24
  have d25 : D 25 < 16 := hD 25 (by decide)
  have c25 : hexc (D 25) < 256 := hexc_lt _ d25
  have d26 : D 26 < 16 := hD 26 (by decide)
  have c26 : hexc (D 26) < 256 := hexc_lt _ d26
  have d27 : D 27 < 16 := hD 27 (by decide)
  have c27 : hexc (D 27) < 256 := hexc_lt _ d27
  have d28 : D 28 < 16 := hD 28 (by decide)
  have c28 : hexc (D 28) < 256 := hexc_lt _ d28
  have d29 : D 29 < 16 := hD 29 (by decide)
  have c29 : hexc (D 29) < 256 := hexc_lt _ d29
  have d30 : D 30 < 16 := hD 30 (by decide)
  have c30 : hexc (D 30) < 256 := hexc_lt _ d30
  have d31 : D 31 < 16 := hD 31 (by decide)
  have c31 : hexc (D 31) < 256 := hexc_lt _ d31
  have hdash : vn dash = 45 := by decide
  obtain ⟨a, ha, va⟩ := take_lanes [H D 31, H D 30, H D 29, H D 28, H D 27, H D 26, H D 25, H D 24]
      [dash, H D 23, H D 22, H D 21, H D 20, dash, H D 19, H D 18, H D 17, H D 16, dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0] (by simp)
  replace va : vn a = lk 8 [hexc (D 31), hexc (D 30), hexc (D 29), hexc (D 28), hexc (D 27), hexc (D 26), hexc (D 25), hexc (D 24)] := by
    rw [va]; simp only [List.map_cons, List.map_nil, hdash, vnH D 31 d31, vnH D 30 d30, vnH D 29 d29, vnH D 28 d28, vnH D 27 d27, vnH D 26 d26, vnH D 25 d25, vnH D 24 d24]
  obtain ⟨b, hb, vb⟩ := take_lanes [dash, H D 23, H D 22, H D 21, H D 20]
      [dash, H D 19, H D 18, H D 17, H D 16, dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0] (by simp)
  replace vb : vn b = lk 8 [45, hexc (D 23), hexc (D 22), hexc (D 21), hexc (D 20)] := by
    rw [vb]; simp only [List.map_cons, List.map_nil, hdash, vnH D 23 d23, vnH D 22 d22, vnH D 21 d21, vnH D 20 d20]
  obtain ⟨c, hc, vc⟩ := take_lanes [dash, H D 19, H D 18, H D 17, H D 16]
      [dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0] (by simp)
  replace vc : vn c = lk 8 [45, hexc (D 19), hexc (D 18), hexc (D 17), hexc (D 16)] := by
    rw [vc]; simp only [List.map_cons, List.map_nil, hdash, vnH D 19 d19, vnH D 18 d18, vnH D 17 d17, vnH D 16 d16]
  obtain ⟨d, hd, vd⟩ := take_lanes [dash, H D 15, H D 14, H D 13, H D 12]
      [dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0] (by simp)
  replace vd : vn d = lk 8 [45, hexc (D 15), hexc (D 14), hexc (D 13), hexc (D 12)] := by
    rw [vd]; simp only [List.map_cons, List.map_nil, hdash, vnH D 15 d15, vnH D 14 d14, vnH D 13 d13, vnH D 12 d12]
  obtain ⟨e, he, ve⟩ := take_lanes [dash, H D 11, H D 10, H D 9, H D 8]
      [H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0] (by simp)
  replace ve : vn e = lk 8 [45, hexc (D 11), hexc (D 10), hexc (D 9), hexc (D 8)] := by
    rw [ve]; simp only [List.map_cons, List.map_nil, hdash, vnH D 11 d11, vnH D 10 d10, vnH D 9 d9, vnH D 8 d8]
  obtain ⟨f, hf, vf⟩ := take_lanes [H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0]
      [] (by simp)
  replace vf : vn f = lk 8 [hexc (D 7), hexc (D 6), hexc (D 5), hexc (D 4), hexc (D 3), hexc (D 2), hexc (D 1), hexc (D 0)] := by
    rw [vf]; simp only [List.map_cons, List.map_nil, hdash, vnH D 7 d7, vnH D 6 d6, vnH D 5 d5, vnH D 4 d4, vnH D 3 d3, vnH D 2 d2, vnH D 1 d1, vnH D 0 d0]
  have ta : takebytes (uuidBytes D) 8 = (a, [dash, H D 23, H D 22, H D 21, H D 20, dash, H D 19, H D 18, H D 17, H D 16, dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0], true) := ha
  have tb : takebytes ([dash, H D 23, H D 22, H D 21, H D 20, dash, H D 19, H D 18, H D 17, H D 16, dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0]) 5 = (b, [dash, H D 19, H D 18, H D 17, H D 16, dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0], true) := hb
  have tc : takebytes ([dash, H D 19, H D 18, H D 17, H D 16, dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0]) 5 = (c, [dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0], true) := hc
  have td : takebytes ([dash, H D 15, H D 14, H D 13, H D 12, dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0]) 5 = (d, [dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0], true) := hd
  have te : takebytes ([dash, H D 11, H D 10, H D 9, H D 8, H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0]) 5 = (e, [H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0], true) := he
  have tf : takebytes ([H D 7, H D 6, H D 5, H D 4, H D 3, H D 2, H D 1, H D 0]) 8 = (f, [], true) := hf
  have ha8 := hexdigits8_hex a (D 31) (D 30) (D 29) (D 28) (D 27) (D 26) (D 25) (D 24) d31 d30 d29 d28 d27 d26 d25 d24 va
  have vw2 := w_lanes b c (hexc (D 23)) (hexc (D 22)) (hexc (D 21)) (hexc (D 20)) (hexc (D 19)) (hexc (D 18)) (hexc (D 17)) (hexc (D 16)) c23 c22 c21 c20 c19 c18 c17 c16 vb vc
  have vw3 := w_lanes d e (hexc (D 15)) (hexc (D 14)) (hexc (D 13)) (hexc (D 12)) (hexc (D 11)) (hexc (D 10)) (hexc (D 9)) (hexc (D 8)) c15 c14 c13 c12 c11 c10 c9 c8 vd ve
  have hw2 := hexdigits8_hex _ (D 23) (D 22) (D 21) (D 20) (D 19) (D 18) (D 17) (D 16) d23 d22 d21 d20 d19 d18 d17 d16 vw2
  have hw3 := hexdigits8_hex _ (D 15) (D 14) (D 13) (D 12) (D 11) (D 10) (D 9) (D 8) d15 d14 d13 d12 d11 d10 d9 d8 vw3
  have hf8 := hexdigits8_hex f (D 7) (D 6) (D 5) (D 4) (D 3) (D 2) (D 1) (D 0) d7 d6 d5 d4 d3 d2 d1 d0 vf
  have hdashes : bor (bor (bor (band b (JInt.lit .u64 0xff)) (shl (band c (JInt.lit .u64 0xff)) 8))
      (shl (band d (JInt.lit .u64 0xff)) 16)) (shl (band e (JInt.lit .u64 0xff)) 24) =
      JInt.lit .u64 (45 * 0x01010101) := by
    apply vn_inj uns_u64
    rw [vn_bor uns_u64, vn_bor uns_u64, vn_bor uns_u64, vn_shl uns_u64, vn_shl uns_u64, vn_shl uns_u64,
      dash_lane b _ _ _ _ vb, dash_lane c _ _ _ _ vc, dash_lane d _ _ _ _ vd, dash_lane e _ _ _ _ ve]
    decide
  refine ⟨UUID.ofPair (bor (shl (IntParse.hexdigits8 a) 32) (IntParse.hexdigits8 (bor (shr b 8) (shl (shr c 8) 32))))
    (bor (shl (IntParse.hexdigits8 (bor (shr d 8) (shl (shr e 8) 32))) 32) (IntParse.hexdigits8 f)), ?_, ?_⟩
  · simp only [parseuuid, ta, tb, tc, td, te, tf, List.isEmpty_nil, Bool.and_self, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, hdashes, bne_self_eq_false, ha8.1, hw2.1, hw3.1, hf8.1]
  · have l1 := ha8.2
    have l2 := hw2.2
    have l3 := hw3.2
    have l4 := hf8.2
    simp only [UUID.ofPair]
    rw [vn_bor uns_u128, vn_shl uns_u128, vn_rem uns_u64 uns_u128, vn_rem uns_u64 uns_u128,
      vn_bor uns_u64, vn_shl uns_u64, vn_bor uns_u64, vn_shl uns_u64, l1, l2, l3, l4,
      or_shift _ _ 32 _ (by omega) (by simp only [IntTy.bits]; omega),
      or_shift _ _ 32 _ (by omega) (by simp only [IntTy.bits]; omega),
      Nat.mod_eq_of_lt (a := _ + _) (by simp only [IntTy.bits]; omega),
      Nat.mod_eq_of_lt (a := _ + _) (by simp only [IntTy.bits]; omega),
      or_shift _ _ 64 _ (by omega) (by simp only [IntTy.bits]; omega)]
    omega

theorem uuidStringRoundtrip_proven : UuidStringRoundtrip := by
  intro u
  have hstr : uuidString u = uuidBytes (fun k => vn (sh k u.value) % 16) := by
    rw [uuidString_eq]
    simp only [nib_eq]
    rfl
  obtain ⟨U, hp, hU⟩ := parse_uuidBytes (fun k => vn (sh k u.value) % 16) (fun _ _ => Nat.mod_lt _ (by decide))
  have hUu : U = u := by
    obtain ⟨v⟩ := U
    obtain ⟨x⟩ := u
    simp only [UUID.mk.injEq]
    apply vn_inj uns_u128
    simp only at hU ⊢
    have hb : vn (sh 0 x) < 2 ^ 128 := vn_lt uns_u128 x
    have e0 : vn (sh 1 x) = vn (sh 0 x) / 16 := sh_succ 0 x
    have e1 : vn (sh 2 x) = vn (sh 1 x) / 16 := sh_succ 1 x
    have e2 : vn (sh 3 x) = vn (sh 2 x) / 16 := sh_succ 2 x
    have e3 : vn (sh 4 x) = vn (sh 3 x) / 16 := sh_succ 3 x
    have e4 : vn (sh 5 x) = vn (sh 4 x) / 16 := sh_succ 4 x
    have e5 : vn (sh 6 x) = vn (sh 5 x) / 16 := sh_succ 5 x
    have e6 : vn (sh 7 x) = vn (sh 6 x) / 16 := sh_succ 6 x
    have e7 : vn (sh 8 x) = vn (sh 7 x) / 16 := sh_succ 7 x
    have e8 : vn (sh 9 x) = vn (sh 8 x) / 16 := sh_succ 8 x
    have e9 : vn (sh 10 x) = vn (sh 9 x) / 16 := sh_succ 9 x
    have e10 : vn (sh 11 x) = vn (sh 10 x) / 16 := sh_succ 10 x
    have e11 : vn (sh 12 x) = vn (sh 11 x) / 16 := sh_succ 11 x
    have e12 : vn (sh 13 x) = vn (sh 12 x) / 16 := sh_succ 12 x
    have e13 : vn (sh 14 x) = vn (sh 13 x) / 16 := sh_succ 13 x
    have e14 : vn (sh 15 x) = vn (sh 14 x) / 16 := sh_succ 14 x
    have e15 : vn (sh 16 x) = vn (sh 15 x) / 16 := sh_succ 15 x
    have e16 : vn (sh 17 x) = vn (sh 16 x) / 16 := sh_succ 16 x
    have e17 : vn (sh 18 x) = vn (sh 17 x) / 16 := sh_succ 17 x
    have e18 : vn (sh 19 x) = vn (sh 18 x) / 16 := sh_succ 18 x
    have e19 : vn (sh 20 x) = vn (sh 19 x) / 16 := sh_succ 19 x
    have e20 : vn (sh 21 x) = vn (sh 20 x) / 16 := sh_succ 20 x
    have e21 : vn (sh 22 x) = vn (sh 21 x) / 16 := sh_succ 21 x
    have e22 : vn (sh 23 x) = vn (sh 22 x) / 16 := sh_succ 22 x
    have e23 : vn (sh 24 x) = vn (sh 23 x) / 16 := sh_succ 23 x
    have e24 : vn (sh 25 x) = vn (sh 24 x) / 16 := sh_succ 24 x
    have e25 : vn (sh 26 x) = vn (sh 25 x) / 16 := sh_succ 25 x
    have e26 : vn (sh 27 x) = vn (sh 26 x) / 16 := sh_succ 26 x
    have e27 : vn (sh 28 x) = vn (sh 27 x) / 16 := sh_succ 27 x
    have e28 : vn (sh 29 x) = vn (sh 28 x) / 16 := sh_succ 28 x
    have e29 : vn (sh 30 x) = vn (sh 29 x) / 16 := sh_succ 29 x
    have e30 : vn (sh 31 x) = vn (sh 30 x) / 16 := sh_succ 30 x
    have e31 : vn (sh 32 x) = vn (sh 31 x) / 16 := sh_succ 31 x
    rw [hU]
    show _ = vn (sh 0 x)
    omega
  have htry : tryparseUUID (uuidString u) = some u := by
    rw [tryparseUUID, hstr, hp, hUu]
  simp only [parseUUID, htry]

end JuliaLean.Base64Uuid
