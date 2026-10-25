import JuliaLean.Base64Uuid.Uuid
import JuliaLean.Base64Uuid.BitLemmas

/-!
`Parsers.ishexdigits8` and `Parsers.hexdigits8` (`base/parsers/ints.jl:40-59`) on eight
lowercase hexadecimal digits: the word passes the check and converts to the value of the
digits, first digit most significant.

A word is handled as byte lanes, `lk 8 [b₀, ..., b₇] = b₀ + 2⁸ b₁ + ... + 2⁵⁶ b₇`. While
every lane stays below `2⁸`, the bitwise operations act lane by lane and additions and
multiplications do not carry between lanes.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- Lanes of `k` bits, lowest first. -/
def lk (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => a + 2 ^ k * lk k l

/-! ### Lanes -/

theorem split_bit (k a y j : Nat) (ha : a < 2 ^ k) :
    (a + 2 ^ k * y).testBit j = if j < k then a.testBit j else y.testBit (j - k) := by
  rw [Nat.add_comm]; exact Nat.testBit_two_pow_mul_add y ha j

theorem split_land {k a b : Nat} (y z : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * y) &&& (b + 2 ^ k * z) = (a &&& b) + 2 ^ k * (y &&& z) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, split_bit k a y j ha, split_bit k b z j hb,
    split_bit k _ _ j (Nat.and_lt_two_pow a hb)]
  by_cases h : j < k <;> simp [h]

theorem split_lor {k a b : Nat} (y z : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * y) ||| (b + 2 ^ k * z) = (a ||| b) + 2 ^ k * (y ||| z) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, split_bit k a y j ha, split_bit k b z j hb,
    split_bit k _ _ j (Nat.or_lt_two_pow ha hb)]
  by_cases h : j < k <;> simp [h]

theorem split_lxor {k a b : Nat} (y z : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a + 2 ^ k * y) ^^^ (b + 2 ^ k * z) = (a ^^^ b) + 2 ^ k * (y ^^^ z) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_xor, split_bit k a y j ha, split_bit k b z j hb,
    split_bit k _ _ j (xor_lt_pow ha hb)]
  by_cases h : j < k <;> simp [h]

theorem lk_map_land (k : Nat) (f g : Nat → Nat) : ∀ l : List Nat, (∀ x ∈ l, f x < 2 ^ k) →
    (∀ x ∈ l, g x < 2 ^ k) → lk k (l.map f) &&& lk k (l.map g) = lk k (l.map fun x => f x &&& g x)
  | [], _, _ => by simp [lk]
  | x :: l, hf, hg => by
    simp only [List.map_cons, lk]
    rw [split_land _ _ (hf x (by simp)) (hg x (by simp)),
      lk_map_land k f g l (fun y hy => hf y (by simp [hy])) (fun y hy => hg y (by simp [hy]))]

theorem lk_map_lor (k : Nat) (f g : Nat → Nat) : ∀ l : List Nat, (∀ x ∈ l, f x < 2 ^ k) →
    (∀ x ∈ l, g x < 2 ^ k) → lk k (l.map f) ||| lk k (l.map g) = lk k (l.map fun x => f x ||| g x)
  | [], _, _ => by simp [lk]
  | x :: l, hf, hg => by
    simp only [List.map_cons, lk]
    rw [split_lor _ _ (hf x (by simp)) (hg x (by simp)),
      lk_map_lor k f g l (fun y hy => hf y (by simp [hy])) (fun y hy => hg y (by simp [hy]))]

theorem lk_map_lxor (k : Nat) (f g : Nat → Nat) : ∀ l : List Nat, (∀ x ∈ l, f x < 2 ^ k) →
    (∀ x ∈ l, g x < 2 ^ k) → lk k (l.map f) ^^^ lk k (l.map g) = lk k (l.map fun x => f x ^^^ g x)
  | [], _, _ => by simp [lk]
  | x :: l, hf, hg => by
    simp only [List.map_cons, lk]
    rw [split_lxor _ _ (hf x (by simp)) (hg x (by simp)),
      lk_map_lxor k f g l (fun y hy => hf y (by simp [hy])) (fun y hy => hg y (by simp [hy]))]

theorem lk_map_add (k : Nat) (f g : Nat → Nat) : ∀ l : List Nat,
    lk k (l.map f) + lk k (l.map g) = lk k (l.map fun x => f x + g x)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, lk]
    rw [← lk_map_add k f g l, Nat.mul_add]
    omega

theorem lk_map_mul (k c : Nat) (f : Nat → Nat) : ∀ l : List Nat,
    c * lk k (l.map f) = lk k (l.map fun x => c * f x)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, lk]
    rw [← lk_map_mul k c f l, Nat.mul_add, Nat.mul_left_comm c (2 ^ k)]

theorem lk_map_congr (k : Nat) (f g : Nat → Nat) : ∀ l : List Nat, (∀ x ∈ l, f x = g x) →
    lk k (l.map f) = lk k (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons, lk]
    rw [h x (by simp), lk_map_congr k f g l (fun y hy => h y (by simp [hy]))]

theorem lk_map_const (k c : Nat) : ∀ l : List Nat, lk k (l.map fun _ => c) = lk k (List.replicate l.length c)
  | [] => rfl
  | x :: l => by simp only [List.map_cons, List.length_cons, List.replicate_succ, lk, lk_map_const k c l]

theorem lk_map_lt (k : Nat) (f : Nat → Nat) : ∀ l : List Nat, (∀ x ∈ l, f x < 2 ^ k) →
    lk k (l.map f) < 2 ^ (k * l.length)
  | [], _ => by simp [lk]
  | x :: l, hf => by
    have ih := lk_map_lt k f l (fun y hy => hf y (by simp [hy]))
    have h2 : 2 ^ k * (lk k (l.map f) + 1) ≤ 2 ^ k * 2 ^ (k * l.length) := Nat.mul_le_mul_left _ ih
    have h3 : 2 ^ (k * (l.length + 1)) = 2 ^ k * 2 ^ (k * l.length) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    have := hf x (by simp)
    simp only [Nat.mul_add, Nat.mul_one] at h2
    simp only [List.map_cons, lk, List.length_cons, h3]
    omega

theorem lk_map_id (k : Nat) (l : List Nat) : lk k (l.map fun x => x) = lk k l := by
  rw [List.map_id']

/-- `(x >> n) & o == (x & (o << n)) >> n`. -/
theorem shr_and (x o n : Nat) : (x / 2 ^ n) &&& o = (x &&& (o * 2 ^ n)) / 2 ^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_and, Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow]

theorem vn_add {t : IntTy} (hu : Uns t) (a b : JInt t) : vn (a + b) = (vn a + vn b) % 2 ^ t.bits := by
  show vn (JInt.wrap t (a.val + b.val)) = _
  rw [val_eq_vn hu a, val_eq_vn hu b, ← Int.natCast_add, vn_wrap hu]

theorem vn_mul {t : IntTy} (hu : Uns t) (a b : JInt t) : vn (a * b) = (vn a * vn b) % 2 ^ t.bits := by
  show vn (JInt.wrap t (a.val * b.val)) = _
  rw [val_eq_vn hu a, val_eq_vn hu b, ← Int.natCast_mul, vn_wrap hu]

/-! ### Words of eight lanes -/

section Lanes8

variable (D : List Nat) (h8 : D.length = 8)
include h8

theorem lt64 (f : Nat → Nat) (hf : ∀ x ∈ D, f x < 2 ^ 8) : lk 8 (D.map f) < 2 ^ IntTy.u64.bits := by
  have := lk_map_lt 8 f D hf
  rw [h8] at this
  exact this

theorem lit_rep (c n : Nat) (h : vn (JInt.lit .u64 n) = lk 8 (List.replicate 8 c)) :
    vn (JInt.lit .u64 n) = lk 8 (D.map fun _ => c) := by
  rw [lk_map_const, h8]; exact h

theorem rep_eq (c n : Nat) (h : lk 8 (List.replicate 8 c) = n) : lk 8 (D.map fun _ => c) = n := by
  rw [lk_map_const, h8]; exact h

end Lanes8

/-! ### Hexadecimal digits -/

/-- The lowercase hexadecimal digit of `d < 16`, as `string(::UUID)` writes it. -/
def hexc (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- Bit 6 of a digit: set for letters. -/
def hexL (d : Nat) : Nat := if d < 10 then 0 else 1

/-- The lane of `bytesin(w, lo, hi)` for a lane `c`, with `a = 0x80 - lo`, `b = 0x7f - hi`. -/
def binLane (a b c : Nat) : Nat := (c + a) &&& ((c + b) ^^^ 255) &&& 128

theorem hex_facts : ∀ d, d < 16 →
    hexc d < 2 ^ 8 ∧ hexc d &&& 128 = 0 ∧ hexc d &&& 64 = 64 * hexL d ∧ hexL d * 9 < 2 ^ 8 ∧
    hexc d &&& 15 < 2 ^ 8 ∧ (hexc d &&& 15) + hexL d * 9 = d ∧
    hexc d + 80 < 2 ^ 8 ∧ hexc d + 70 < 2 ^ 8 ∧ (hexc d ||| 32) + 31 < 2 ^ 8 ∧ (hexc d ||| 32) + 25 < 2 ^ 8 ∧
    hexc d ||| 32 < 2 ^ 8 ∧
    binLane 80 70 (hexc d) ||| binLane 31 25 (hexc d ||| 32) = 128 := by
  decide

theorem bin_lt (a b c : Nat) : binLane a b c < 2 ^ 8 := Nat.and_lt_two_pow _ (by decide)

/-- `bytesin(w, lo, hi)` on lanes `F x` with `F x + a, F x + b < 2⁸`. -/
theorem bytesin_lk (D : List Nat) (h8 : D.length = 8) (F : Nat → Nat) (w : JInt .u64)
    (hw : vn w = lk 8 (D.map F)) (lo hi : Byte) (a b : Nat)
    (ha : vn (JInt.rem .u64 (IntParse.byte 0x80 - lo)) = a) (hb : vn (JInt.rem .u64 (IntParse.byte 0x7f - hi)) = b)
    (hFa : ∀ x ∈ D, F x + a < 2 ^ 8) (hFb : ∀ x ∈ D, F x + b < 2 ^ 8) :
    vn (IntParse.bytesin w lo hi) = lk 8 (D.map fun x => binLane a b (F x)) := by
  have hones : vn (JInt.lit .u64 0x0101010101010101) = lk 8 (D.map fun _ => 1) :=
    lit_rep D h8 1 _ (by decide)
  have hff : vn (JInt.lit .u64 0xffffffffffffffff) = lk 8 (D.map fun _ => 255) :=
    lit_rep D h8 255 _ (by decide)
  have h80 : vn (JInt.lit .u64 0x8080808080808080) = lk 8 (D.map fun _ => 128) :=
    lit_rep D h8 128 _ (by decide)
  have hF : ∀ x ∈ D, F x < 2 ^ 8 := fun x hx => by have := hFa x hx; omega
  -- `w + c * ones` for a constant `c` that does not carry
  have hsum : ∀ c : JInt .u64, (∀ x ∈ D, F x + vn c < 2 ^ 8) →
      vn (w + c * JInt.lit .u64 0x0101010101010101) = lk 8 (D.map fun x => F x + vn c) := by
    intro c hc
    have hc8 : ∀ x ∈ D, vn c * 1 < 2 ^ 8 := fun x hx => by have := hc x hx; omega
    rw [vn_add uns_u64, vn_mul uns_u64, hones, hw, lk_map_mul, Nat.mod_eq_of_lt (lt64 D h8 (fun _ => vn c * 1) hc8),
      lk_map_add, Nat.mod_eq_of_lt (lt64 D h8 (fun x => F x + vn c * 1) (fun x hx => by have := hc x hx; omega))]
    exact lk_map_congr 8 _ _ D (fun x _ => by simp)
  have hA := hsum (JInt.rem .u64 (IntParse.byte 0x80 - lo)) (by rw [ha]; exact hFa)
  have hB := hsum (JInt.rem .u64 (IntParse.byte 0x7f - hi)) (by rw [hb]; exact hFb)
  rw [ha] at hA
  rw [hb] at hB
  simp only [IntParse.bytesin]
  rw [vn_band uns_u64, vn_band uns_u64, vn_bxor uns_u64, hA, hB, hff, h80,
    lk_map_lxor 8 (fun x => F x + b) (fun _ => 255) D hFb (fun _ _ => by decide),
    lk_map_land 8 (fun x => F x + a) (fun x => (F x + b) ^^^ 255) D hFa
      (fun x hx => xor_lt_pow (hFb x hx) (by decide)),
    lk_map_land 8 (fun x => (F x + a) &&& ((F x + b) ^^^ 255)) (fun _ => 128) D
      (fun x hx => Nat.and_lt_two_pow _ (xor_lt_pow (hFb x hx) (by decide))) (fun _ _ => by decide)]
  rfl

theorem ishexdigits8_hex (D : List Nat) (h8 : D.length = 8) (hD : ∀ x ∈ D, x < 16) (w : JInt .u64)
    (hw : vn w = lk 8 (D.map hexc)) : IntParse.ishexdigits8 w = true := by
  have hf := fun (x : Nat) (hx : x ∈ D) => hex_facts x (hD x hx)
  have h80 : vn (JInt.lit .u64 0x8080808080808080) = lk 8 (D.map fun _ => 128) :=
    lit_rep D h8 128 _ (by decide)
  have h20 : vn (JInt.lit .u64 0x2020202020202020) = lk 8 (D.map fun _ => 32) :=
    lit_rep D h8 32 _ (by decide)
  have hhex : ∀ x ∈ D, hexc x < 2 ^ 8 := fun x hx => (hf x hx).1
  have hand : vn (band w (JInt.lit .u64 0x8080808080808080)) = 0 := by
    rw [vn_band uns_u64, hw, h80, lk_map_land 8 hexc (fun _ => 128) D hhex (fun _ _ => by decide),
      lk_map_congr 8 (fun x => hexc x &&& 128) (fun _ => 0) D (fun x hx => (hf x hx).2.1)]
    exact rep_eq D h8 0 0 (by decide)
  have hw2 : vn (bor w (JInt.lit .u64 0x2020202020202020)) = lk 8 (D.map fun x => hexc x ||| 32) := by
    rw [vn_bor uns_u64, hw, h20, lk_map_lor 8 hexc (fun _ => 32) D hhex (fun _ _ => by decide)]
  have b1 := bytesin_lk D h8 hexc w hw (IntParse.byte 48) (IntParse.byte 57) 80 70 (by decide) (by decide)
    (fun x hx => (hf x hx).2.2.2.2.2.2.1) (fun x hx => (hf x hx).2.2.2.2.2.2.2.1)
  have b2 := bytesin_lk D h8 (fun x => hexc x ||| 32) _ hw2 (IntParse.byte 97) (IntParse.byte 102) 31 25
    (by decide) (by decide)
    (fun x hx => (hf x hx).2.2.2.2.2.2.2.2.1) (fun x hx => (hf x hx).2.2.2.2.2.2.2.2.2.1)
  have hor : vn (bor (IntParse.bytesin w (IntParse.byte 48) (IntParse.byte 57))
      (IntParse.bytesin (bor w (JInt.lit .u64 0x2020202020202020)) (IntParse.byte 97) (IntParse.byte 102))) =
      0x8080808080808080 := by
    rw [vn_bor uns_u64, b1, b2, lk_map_lor 8 (fun x => binLane 80 70 (hexc x)) (fun x => binLane 31 25 (hexc x ||| 32))
        D (fun _ _ => bin_lt _ _ _) (fun _ _ => bin_lt _ _ _),
      lk_map_congr 8 (fun x => binLane 80 70 (hexc x) ||| binLane 31 25 (hexc x ||| 32)) (fun _ => 128) D
        (fun x hx => (hf x hx).2.2.2.2.2.2.2.2.2.2.2)]
    exact rep_eq D h8 128 _ (by decide)
  simp only [IntParse.ishexdigits8, val_eq_vn uns_u64, hand, hor]
  all_goals decide

/-- The first step of `hexdigits8`: each lane becomes its digit's value. -/
theorem hexdigits8_step1 (D : List Nat) (h8 : D.length = 8) (hD : ∀ x ∈ D, x < 16) (w : JInt .u64)
    (hw : vn w = lk 8 (D.map hexc)) :
    vn (band w (JInt.lit .u64 0x0f0f0f0f0f0f0f0f) +
      band (shr w 6) (JInt.lit .u64 0x0101010101010101) * JInt.lit .u64 9) = lk 8 D := by
  have hf := fun (x : Nat) (hx : x ∈ D) => hex_facts x (hD x hx)
  have hhex : ∀ x ∈ D, hexc x < 2 ^ 8 := fun x hx => (hf x hx).1
  have h0f : vn (JInt.lit .u64 0x0f0f0f0f0f0f0f0f) = lk 8 (D.map fun _ => 15) := lit_rep D h8 15 _ (by decide)
  have h01 : vn (JInt.lit .u64 0x0101010101010101) = lk 8 (D.map fun _ => 1) := lit_rep D h8 1 _ (by decide)
  have h40 : lk 8 (D.map fun _ => 1) * 2 ^ 6 = lk 8 (D.map fun _ => 64) := by
    rw [lk_map_const, lk_map_const, h8]; decide
  have hL : vn (band (shr w 6) (JInt.lit .u64 0x0101010101010101)) = lk 8 (D.map hexL) := by
    rw [vn_band uns_u64, vn_shr uns_u64, h01, shr_and, h40, hw,
      lk_map_land 8 hexc (fun _ => 64) D hhex (fun _ _ => by decide),
      lk_map_congr 8 (fun x => hexc x &&& 64) (fun x => 64 * hexL x) D (fun x hx => (hf x hx).2.2.1),
      ← lk_map_mul 8 64 hexL D]
    exact Nat.mul_div_cancel_left _ (by decide)
  have h9 : vn (JInt.lit .u64 9) = 9 := by decide
  have hlt : lk 8 D < 2 ^ IntTy.u64.bits := by
    have := lt64 D h8 (fun x => x) (fun x hx => by have := hD x hx; omega)
    rwa [lk_map_id] at this
  rw [vn_add uns_u64, vn_mul uns_u64, hL, h9, vn_band uns_u64, hw, h0f,
    lk_map_land 8 hexc (fun _ => 15) D hhex (fun _ _ => by decide), Nat.mul_comm (lk 8 (D.map hexL)) 9,
    lk_map_mul 8 9 hexL D,
    Nat.mod_eq_of_lt (lt64 D h8 (fun x => 9 * hexL x) (fun x hx => by rw [Nat.mul_comm]; exact (hf x hx).2.2.2.1)),
    lk_map_add,
    lk_map_congr 8 (fun x => (hexc x &&& 15) + 9 * hexL x) (fun x => x) D
      (fun x hx => by rw [Nat.mul_comm 9]; exact (hf x hx).2.2.2.2.2.1), lk_map_id,
    Nat.mod_eq_of_lt hlt]

/-! ### Combining lanes -/

theorem lk_zip_lor (k : Nat) (a b : List Nat) (hl : a.length = b.length) (ha : ∀ x ∈ a, x < 2 ^ k)
    (hb : ∀ x ∈ b, x < 2 ^ k) : lk k a ||| lk k b = lk k (List.zipWith (· ||| ·) a b) := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [lk]
  | cons x a ih =>
    cases b with
    | nil => simp at hl
    | cons y b =>
      simp only [lk, List.zipWith_cons_cons]
      rw [split_lor _ _ (ha x (by simp)) (hb y (by simp)),
        ih b (by simpa using hl) (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz]))]

theorem lk_zip_land (k : Nat) (a b : List Nat) (hl : a.length = b.length) (ha : ∀ x ∈ a, x < 2 ^ k)
    (hb : ∀ x ∈ b, x < 2 ^ k) : lk k a &&& lk k b = lk k (List.zipWith (· &&& ·) a b) := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [lk]
  | cons x a ih =>
    cases b with
    | nil => simp at hl
    | cons y b =>
      simp only [lk, List.zipWith_cons_cons]
      rw [split_land _ _ (ha x (by simp)) (hb y (by simp)),
        ih b (by simpa using hl) (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz]))]

theorem or16 (a b : Nat) (hb : b < 16) : 16 * a ||| b = 16 * a + b :=
  (Nat.two_pow_add_eq_or_of_lt (i := 4) hb a).symm

theorem and255 (x : Nat) (h : x < 256) : x &&& 255 = x := by
  rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt h

theorem or16_and255 (a b : Nat) (ha : a < 16) (hb : b < 16) : (16 * a ||| b) &&& 255 = 16 * a + b := by
  rw [or16 a b hb, and255 _ (by omega)]

theorem hexdigits8_step2 (x : JInt .u64) (d0 d1 d2 d3 d4 d5 d6 d7 : Nat) (h0 : d0 < 16) (h1 : d1 < 16)
    (h2 : d2 < 16) (h3 : d3 < 16) (h4 : d4 < 16) (h5 : d5 < 16) (h6 : d6 < 16) (h7 : d7 < 16)
    (hx : vn x = lk 8 [d0, d1, d2, d3, d4, d5, d6, d7]) :
    vn (band (bor (shl x 4) (shr x 8)) (JInt.lit .u64 0x00ff00ff00ff00ff)) =
      lk 8 [16 * d0 + d1, 0, 16 * d2 + d3, 0, 16 * d4 + d5, 0, 16 * d6 + d7, 0] := by
  have hs : vn (shl x 4) = lk 8 [16 * d0, 16 * d1, 16 * d2, 16 * d3, 16 * d4, 16 * d5, 16 * d6, 16 * d7] := by
    rw [vn_shl uns_u64, hx]; simp only [lk, IntTy.bits]; omega
  have hr : vn (shr x 8) = lk 8 [d1, d2, d3, d4, d5, d6, d7, 0] := by
    rw [vn_shr uns_u64, hx]; simp only [lk]; omega
  have hm : vn (JInt.lit .u64 0x00ff00ff00ff00ff) = lk 8 [255, 0, 255, 0, 255, 0, 255, 0] := by decide
  rw [vn_band uns_u64, vn_bor uns_u64, hs, hr, hm,
    lk_zip_lor 8 [16 * d0, 16 * d1, 16 * d2, 16 * d3, 16 * d4, 16 * d5, 16 * d6, 16 * d7] [d1, d2, d3, d4, d5, d6, d7, 0] rfl (by intro z hz; simp at hz ⊢; omega) (by intro z hz; simp at hz ⊢; omega)]
  simp only [List.zipWith]
  rw [lk_zip_land 8 [16 * d0 ||| d1, 16 * d1 ||| d2, 16 * d2 ||| d3, 16 * d3 ||| d4, 16 * d4 ||| d5, 16 * d5 ||| d6, 16 * d6 ||| d7, 16 * d7 ||| 0] [255, 0, 255, 0, 255, 0, 255, 0] rfl
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with h | h | h | h | h | h | h | h <;> subst h <;> exact Nat.or_lt_two_pow (by omega) (by omega)) (by intro z hz; simp at hz ⊢; omega)]
  simp only [List.zipWith, or16_and255, h0, h1, h2, h3, h4, h5, h6, h7,
    Nat.or_zero, Nat.and_zero]

theorem hexdigits8_step3 (x : JInt .u64) (e0 e1 e2 e3 : Nat) (h0 : e0 < 256) (h1 : e1 < 256)
    (h2 : e2 < 256) (h3 : e3 < 256) (hx : vn x = lk 8 [e0, 0, e1, 0, e2, 0, e3, 0]) :
    vn (band (bor (shl x 8) (shr x 16)) (JInt.lit .u64 0x0000ffff0000ffff)) =
      lk 8 [e1, e0, 0, 0, e3, e2, 0, 0] := by
  have hs : vn (shl x 8) = lk 8 [0, e0, 0, e1, 0, e2, 0, e3] := by
    rw [vn_shl uns_u64, hx]; simp only [lk, IntTy.bits]; omega
  have hr : vn (shr x 16) = lk 8 [e1, 0, e2, 0, e3, 0, 0, 0] := by
    rw [vn_shr uns_u64, hx]; simp only [lk]; omega
  have hm : vn (JInt.lit .u64 0x0000ffff0000ffff) = lk 8 [255, 255, 0, 0, 255, 255, 0, 0] := by decide
  rw [vn_band uns_u64, vn_bor uns_u64, hs, hr, hm,
    lk_zip_lor 8 [0, e0, 0, e1, 0, e2, 0, e3] [e1, 0, e2, 0, e3, 0, 0, 0] rfl (by intro z hz; simp at hz ⊢; omega) (by intro z hz; simp at hz ⊢; omega)]
  simp only [List.zipWith]
  rw [lk_zip_land 8 [0 ||| e1, e0 ||| 0, 0 ||| e2, e1 ||| 0, 0 ||| e3, e2 ||| 0, 0 ||| 0, e3 ||| 0] [255, 255, 0, 0, 255, 255, 0, 0] rfl (by intro z hz; simp at hz ⊢; omega) (by intro z hz; simp at hz ⊢; omega)]
  simp only [List.zipWith, Nat.or_zero, Nat.zero_or, Nat.and_zero,
    and255 e0 h0, and255 e1 h1, and255 e2 h2, and255 e3 h3]

theorem hexdigits8_step4 (x : JInt .u64) (e0 e1 e2 e3 : Nat) (h0 : e0 < 256) (h1 : e1 < 256)
    (h2 : e2 < 256) (h3 : e3 < 256) (hx : vn x = lk 8 [e1, e0, 0, 0, e3, e2, 0, 0]) :
    vn (band (bor (shl x 16) (shr x 32)) (JInt.lit .u64 0x00000000ffffffff)) =
      lk 8 [e3, e2, e1, e0, 0, 0, 0, 0] := by
  have hs : vn (shl x 16) = lk 8 [0, 0, e1, e0, 0, 0, e3, e2] := by
    rw [vn_shl uns_u64, hx]; simp only [lk, IntTy.bits]; omega
  have hr : vn (shr x 32) = lk 8 [e3, e2, 0, 0, 0, 0, 0, 0] := by
    rw [vn_shr uns_u64, hx]; simp only [lk]; omega
  have hm : vn (JInt.lit .u64 0x00000000ffffffff) = lk 8 [255, 255, 255, 255, 0, 0, 0, 0] := by decide
  rw [vn_band uns_u64, vn_bor uns_u64, hs, hr, hm,
    lk_zip_lor 8 [0, 0, e1, e0, 0, 0, e3, e2] [e3, e2, 0, 0, 0, 0, 0, 0] rfl (by intro z hz; simp at hz ⊢; omega) (by intro z hz; simp at hz ⊢; omega)]
  simp only [List.zipWith]
  rw [lk_zip_land 8 [0 ||| e3, 0 ||| e2, e1 ||| 0, e0 ||| 0, 0 ||| 0, 0 ||| 0, e3 ||| 0, e2 ||| 0] [255, 255, 255, 255, 0, 0, 0, 0] rfl (by intro z hz; simp at hz ⊢; omega) (by intro z hz; simp at hz ⊢; omega)]
  simp only [List.zipWith, Nat.or_zero, Nat.zero_or, Nat.and_zero,
    and255 e0 h0, and255 e1 h1, and255 e2 h2, and255 e3 h3]

/-- `ishexdigits8` accepts eight lowercase hex digits (first in the lowest byte) and
`hexdigits8` returns their value, first digit most significant. -/
theorem hexdigits8_hex (w : JInt .u64) (d0 d1 d2 d3 d4 d5 d6 d7 : Nat) (h0 : d0 < 16) (h1 : d1 < 16)
    (h2 : d2 < 16) (h3 : d3 < 16) (h4 : d4 < 16) (h5 : d5 < 16) (h6 : d6 < 16) (h7 : d7 < 16)
    (hw : vn w = lk 8 [hexc d0, hexc d1, hexc d2, hexc d3, hexc d4, hexc d5, hexc d6, hexc d7]) :
    IntParse.ishexdigits8 w = true ∧
      vn (IntParse.hexdigits8 w) = ((((((d0 * 16 + d1) * 16 + d2) * 16 + d3) * 16 + d4) * 16 + d5) * 16 + d6) * 16 + d7 := by
  have hD : ∀ x ∈ [d0, d1, d2, d3, d4, d5, d6, d7], x < 16 := by intro z hz; simp at hz; omega
  refine ⟨ishexdigits8_hex _ rfl hD w hw, ?_⟩
  have s1 := hexdigits8_step1 _ rfl hD w hw
  have s2 := hexdigits8_step2 _ d0 d1 d2 d3 d4 d5 d6 d7 h0 h1 h2 h3 h4 h5 h6 h7 s1
  have s3 := hexdigits8_step3 _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) s2
  have s4 := hexdigits8_step4 _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) s3
  rw [show vn (IntParse.hexdigits8 w) = lk 8 [_, _, _, _, 0, 0, 0, 0] from s4]
  simp only [lk]
  omega

end JuliaLean.Base64Uuid
