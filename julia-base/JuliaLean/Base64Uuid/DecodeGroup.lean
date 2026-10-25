import JuliaLean.Base64Uuid.EncodeProofs
import JuliaLean.Base64Uuid.BitLemmas

/-!
Group-level decoding: the bytes `decode_slow` emits for a quadruplet of characters
without ignored characters, and the fact that they invert the encoder's groups.
-/

set_option maxRecDepth 100000

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- The bytes `decode_slow` (`decode.jl:158-179`) emits for the decoded quadruplet
`d1..d4` when none of them is `CODE_IGN`; `none` where it throws. -/
def quadBytes (d1 d2 d3 d4 : Byte) : Option (List Byte) :=
  if isCode d1 && isCode d2 && isCode d3 && isCode d4 then
    some [bor (shl d1 2) (shr d2 4), bor (shl d2 4) (shr d3 2), bor (shl d3 6) d4]
  else if isCode d1 && isCode d2 && isCode d3 && padOrEnd d4 then
    some [bor (shl d1 2) (shr d2 4), bor (shl d2 4) (shr d3 2)]
  else if isCode d1 && isCode d2 && padOrEnd d3 && padOrEnd d4 then
    some [bor (shl d1 2) (shr d2 4)]
  else if d1 == CODE_END && d2 == CODE_END && d3 == CODE_END && d4 == CODE_END then some []
  else none

/-- A complete group: four alphabet characters. -/
def FullG (c1 c2 c3 c4 : Byte) : Prop :=
  isCode (decode c1) = true ∧ isCode (decode c2) = true ∧ isCode (decode c3) = true ∧
    isCode (decode c4) = true

/-- A final group with one or two padding characters. -/
def PadG (c1 c2 c3 c4 : Byte) : Prop :=
  isCode (decode c1) = true ∧ isCode (decode c2) = true ∧
    ((isCode (decode c3) = true ∧ decode c4 = CODE_PAD) ∨ (decode c3 = CODE_PAD ∧ decode c4 = CODE_PAD))

/-- Characters made of complete groups, possibly ending in one padded group. -/
def Clean : List Byte → Prop
  | [] => True
  | c1 :: c2 :: c3 :: c4 :: rest => (FullG c1 c2 c3 c4 ∧ Clean rest) ∨ (rest = [] ∧ PadG c1 c2 c3 c4)
  | _ => False

/-- The bytes of the groups of a clean character list. -/
def specDec : List Byte → List Byte
  | c1 :: c2 :: c3 :: c4 :: rest =>
    (quadBytes (decode c1) (decode c2) (decode c3) (decode c4)).getD [] ++ specDec rest
  | _ => []

theorem b8_vn (y : Byte) : b8 (vn y) = y := by
  apply vn_inj uns_u8
  show vn (JInt.wrap .u8 ((vn y : Nat) : Int)) = vn y
  rw [vn_wrap uns_u8]
  exact Nat.mod_eq_of_lt (vn_lt uns_u8 y)

theorem decode_encode_table : ∀ n : Fin 256, decode (encode (b8 n)) = band (b8 n) (b8 0x3f) := by
  decide

theorem decode_encode (y : Byte) : decode (encode y) = band y (b8 0x3f) := by
  have h := decode_encode_table ⟨vn y, vn_lt uns_u8 y⟩
  simp only [b8_vn] at h
  exact h

theorem decode_pad : decode encodepadding = CODE_PAD := by decide

theorem and63 (x : Nat) : x &&& 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem orsum (x y k : Nat) (hx : x % 2 ^ k = 0) (hy : y < 2 ^ k) : x ||| y = x + y := by
  have : x = 2 ^ k * (x / 2 ^ k) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)).symm
  rw [this, ← Nat.two_pow_add_eq_or_of_lt hy]

theorem isCode_band63 (y : Byte) : isCode (band y (b8 0x3f)) = true := by
  have h : vn (band y (b8 0x3f)) < 64 := by
    rw [vn_band uns_u8]; exact Nat.and_lt_two_pow _ (show vn (b8 0x3f) < 2 ^ 6 by decide)
  have h2 := val_eq_vn uns_u8 (band y (b8 0x3f))
  simp only [isCode, decide_eq_true_eq]
  show (band y (b8 0x3f)).val < 64
  omega

theorem isCode_pad : isCode CODE_PAD = false := by decide
theorem padOrEnd_pad : padOrEnd CODE_PAD = true := by decide

/-- The first byte of a group: `(c1 << 2) | (c2 >> 4)` with `c1 = (b1 >> 2) & 0x3f` and
`c2 = ((b1 << 4) | t) & 0x3f`, `t < 16`. -/
theorem out1_eq (b1 t : Byte) (ht : vn t < 16) :
    bor (shl (band (shr b1 2) (b8 0x3f)) 2) (shr (band (bor (shl b1 4) t) (b8 0x3f)) 4) = b1 := by
  apply vn_inj uns_u8
  have hb : vn b1 < 256 := vn_lt uns_u8 b1
  simp only [vn_bor uns_u8, vn_shl uns_u8, vn_band uns_u8, vn_shr uns_u8]
  show (vn b1 / 4 &&& 63) * 4 % 256 ||| ((vn b1 * 16 % 256 ||| vn t) &&& 63) / 16 = vn b1
  rw [and63, and63, orsum (vn b1 * 16 % 256) (vn t) 4 (by omega) (by simpa using ht)]
  rw [orsum ((vn b1 / 4 % 64) * 4 % 256) ((vn b1 * 16 % 256 + vn t) % 64 / 16) 2 (by omega)
    (by simp; omega)]
  omega

/-- The second byte: `(c2 << 4) | (c3 >> 2)` with `c2 = ((b1 << 4) | (b2 >> 4)) & 0x3f`
and `c3 = ((b2 << 2) | t) & 0x3f`, `t < 4`. -/
theorem out2_eq (b1 b2 t : Byte) (ht : vn t < 4) :
    bor (shl (band (bor (shl b1 4) (shr b2 4)) (b8 0x3f)) 4) (shr (band (bor (shl b2 2) t) (b8 0x3f)) 2) = b2 := by
  apply vn_inj uns_u8
  have hb1 : vn b1 < 256 := vn_lt uns_u8 b1
  have hb2 : vn b2 < 256 := vn_lt uns_u8 b2
  simp only [vn_bor uns_u8, vn_shl uns_u8, vn_band uns_u8, vn_shr uns_u8]
  show ((vn b1 * 16 % 256 ||| vn b2 / 16) &&& 63) * 16 % 256 ||| ((vn b2 * 4 % 256 ||| vn t) &&& 63) / 4
    = vn b2
  rw [and63, and63, orsum (vn b1 * 16 % 256) (vn b2 / 16) 4 (by omega) (by simp; omega),
    orsum (vn b2 * 4 % 256) (vn t) 2 (by omega) (by simpa using ht)]
  rw [orsum ((vn b1 * 16 % 256 + vn b2 / 16) % 64 * 16 % 256) ((vn b2 * 4 % 256 + vn t) % 64 / 4) 4
    (by omega) (by simp; omega)]
  omega

/-- The third byte: `(c3 << 6) | c4` with `c3 = ((b2 << 2) | (b3 >> 6)) & 0x3f` and
`c4 = b3 & 0x3f`. -/
theorem out3_eq (b2 b3 : Byte) :
    bor (shl (band (bor (shl b2 2) (shr b3 6)) (b8 0x3f)) 6) (band b3 (b8 0x3f)) = b3 := by
  apply vn_inj uns_u8
  have hb2 : vn b2 < 256 := vn_lt uns_u8 b2
  have hb3 : vn b3 < 256 := vn_lt uns_u8 b3
  simp only [vn_bor uns_u8, vn_shl uns_u8, vn_band uns_u8, vn_shr uns_u8]
  show ((vn b2 * 4 % 256 ||| vn b3 / 64) &&& 63) * 64 % 256 ||| (vn b3 &&& 63) = vn b3
  rw [and63, and63, orsum (vn b2 * 4 % 256) (vn b3 / 64) 2 (by omega) (by simp; omega)]
  rw [orsum ((vn b2 * 4 % 256 + vn b3 / 64) % 64 * 64 % 256) (vn b3 % 64) 6 (by omega) (by simp; omega)]
  omega

theorem shr4_lt (b : Byte) : vn (shr b 4) < 16 := by
  rw [vn_shr uns_u8]; have : vn b < 256 := vn_lt uns_u8 b; show vn b / 16 < 16; omega

theorem shr6_lt (b : Byte) : vn (shr b 6) < 4 := by
  rw [vn_shr uns_u8]; have : vn b < 256 := vn_lt uns_u8 b; show vn b / 64 < 4; omega

theorem zero_lt4 : vn (b8 0) < 4 := by decide
theorem zero_lt16 : vn (b8 0) < 16 := by decide

theorem bor_zero (x : Byte) : bor x (b8 0) = x := by
  apply vn_inj uns_u8; rw [vn_bor uns_u8, show vn (b8 0) = 0 from rfl, Nat.or_zero]

theorem quad_full (b1 b2 b3 : Byte) :
    quadBytes (decode (encode (shr b1 2))) (decode (encode (bor (shl b1 4) (shr b2 4))))
      (decode (encode (bor (shl b2 2) (shr b3 6)))) (decode (encode b3)) = some [b1, b2, b3] := by
  simp only [decode_encode, quadBytes, isCode_band63, Bool.and_self, ↓reduceIte]
  rw [out1_eq b1 _ (shr4_lt b2), out2_eq b1 b2 _ (shr6_lt b3), out3_eq b2 b3]

theorem quad_pad1 (b1 : Byte) :
    quadBytes (decode (encode (shr b1 2))) (decode (encode (shl b1 4))) (decode encodepadding)
      (decode encodepadding) = some [b1] := by
  simp only [decode_encode, decode_pad, quadBytes, isCode_band63, isCode_pad, padOrEnd_pad,
    Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have := out1_eq b1 (b8 0) zero_lt16
  rw [bor_zero] at this
  rw [this]

theorem quad_pad2 (b1 b2 : Byte) :
    quadBytes (decode (encode (shr b1 2))) (decode (encode (bor (shl b1 4) (shr b2 4))))
      (decode (encode (shl b2 2))) (decode encodepadding) = some [b1, b2] := by
  simp only [decode_encode, decode_pad, quadBytes, isCode_band63, isCode_pad, padOrEnd_pad,
    Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have := out2_eq b1 b2 (b8 0) zero_lt4
  rw [bor_zero] at this
  rw [out1_eq b1 _ (shr4_lt b2), this]

theorem specDec_encFull : ∀ (full rest : List Byte), full.length % 3 = 0 →
    specDec (encFull full ++ rest) = full ++ specDec rest
  | [], rest, _ => by simp [encFull]
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | b1 :: b2 :: b3 :: full, rest, h => by
    simp only [encFull, enc4, List.cons_append, specDec, quad_full, Option.getD_some, List.nil_append]
    rw [specDec_encFull full rest (by simp at h; omega)]

theorem close_tail (tail : List Byte) (ht : tail.length ≤ 2) :
    specDec (close ⟨[], tail⟩) = tail := by
  match tail, ht with
  | [], _ => rfl
  | [b1], _ =>
    simp only [close, loadtriplet]
    simp [specDec, quad_pad1]
  | [b1, b2], _ =>
    simp only [close, loadtriplet]
    simp [specDec, quad_pad2]

theorem specDec_base64encode (x : List Byte) : specDec (base64encode x) = x := by
  obtain ⟨full, tail, hx, hf, ht, he⟩ := base64encode_split x
  rw [he, specDec_encFull _ _ hf, close_tail _ ht, hx]

end JuliaLean.Base64Uuid
