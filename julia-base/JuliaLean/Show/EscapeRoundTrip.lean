import JuliaLean.Show.EscapeProofs
import JuliaLean.MissingChar.CharProofs

/-!
# `unescape_string(escape_string(s)) == s` away from code points above `0x10ffff`

`escapeRoundTrip_refuted` (`EscapeProofs.lean`) shows that the round trip fails
for a well-formed char whose code point exceeds `0x10ffff`. This file proves
that such chars are the only obstruction: for every other string short enough
that the escaped copy can be allocated, `unescape_string(escape_string(s))`
returns the bytes of `s`.

The chars of `s` fall into three classes (`classify`): ASCII chars (`IsA`),
malformed or overlong chars, escaped byte by byte as `\xHH` (`IsX`), and
well-formed chars with a code point in `0x80:0x10ffff` (`IsM`), printed raw or as
`\u`/`\U` escapes. Each char becomes a piece of the escaped string
(`escCharC`) that is ASCII or one raw well-formed char, so iterating the escaped
string yields exactly the pieces (`chars_of_complete`), and one or more steps of
the `unescape_string` loop turn each piece back into the bytes of its char
(`PieceOK`).
-/

namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-- `unescape_string(escape_string(s)) == s` with the default arguments for every
string `s` none of whose chars is a well-formed, non-overlong char with a code
point above `0x10ffff`, and that is short enough (`< 2^59` bytes) for the
escaped copy, at most four times longer, to be allocated. -/
def EscapeRoundTripInRange : Prop :=
  ∀ (d : UData) (s : JStr), s.bytes.length < 2 ^ 59 →
    (∀ c ∈ chars s, ¬ (ismalformed c = false ∧ isoverlong c = false ∧
      ∃ u, codepoint c = .ok u ∧ u > 0x10ffff)) →
    ∃ r t, escapeString d s = .ok r ∧ unescapeString r = .ok t ∧ t.bytes = s.bytes

namespace EscRT

open JuliaLean.MissingChar.CharPf (enc b4 dec_all charOfU32_ok eq_ofNat isoverlong_nat clo32_3 clo32_4
  ctz32_range land56_eq)

/-! ## One `iterate` step on a byte list -/

/-- One step of `iterate(s::String, i)` (`base/strings/string.jl:508-538`) on the
bytes `L` of `s` from index `i` on: the char and the number of bytes it spans. -/
def decAt (L : List UInt8) : UInt32 × Nat :=
  let b := L.getD 0 0
  let u := b.toUInt32 <<< 24
  if !between b 0x80 0xf7 then (u, 1)
  else if u < 0xc0000000 then (u, 1)
  else if 1 ≥ L.length then (u, 1)
  else
    let b := L.getD 1 0
    if !isCont b then (u, 1)
    else
      let u := u ||| (b.toUInt32 <<< 16)
      if decide (2 ≥ L.length) || decide (u < 0xe0000000) then (u, 2)
      else
        let b := L.getD 2 0
        if !isCont b then (u, 2)
        else
          let u := u ||| (b.toUInt32 <<< 8)
          if decide (3 ≥ L.length) || decide (u < 0xf0000000) then (u, 3)
          else
            let b := L.getD 3 0
            if !isCont b then (u, 3)
            else (u ||| b.toUInt32, 4)

theorem getD_drop0 (L : List UInt8) (n k : Nat) : (L.drop n).getD k 0 = L.getD (n + k) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem iterate_dec (s : JStr) (p : JInt64) (h1 : 1 ≤ p.val) (h2 : p.val ≤ s.bytes.length) :
    ∃ j, iterate s p = some ((decAt (s.bytes.drop (p.val.toNat - 1))).1, j) ∧
      j.val = p.val + (decAt (s.bytes.drop (p.val.toNat - 1))).2 := by
  have hs := ncu_small s
  have e1 : (p + ix 1).val = p.val + 1 := add1_val _ (by omega) (by omega)
  have e2 : (p + ix 1 + ix 1).val = p.val + 2 := by rw [add1_val _ (by omega) (by omega), e1]; omega
  have e3 : (p + ix 1 + ix 1 + ix 1).val = p.val + 3 := by rw [add1_val _ (by omega) (by omega), e2]; omega
  have e4 : (p + ix 1 + ix 1 + ix 1 + ix 1).val = p.val + 4 := by
    rw [add1_val _ (by omega) (by omega), e3]; omega
  have hB1 : cu s (p + ix 1) = s.bytes.getD (p.val.toNat - 1 + 1) 0 := by rw [cu_eq, e1]; congr 1; omega
  have hB2 : cu s (p + ix 1 + ix 1) = s.bytes.getD (p.val.toNat - 1 + 2) 0 := by
    rw [cu_eq, e2]; congr 1; omega
  have hB3 : cu s (p + ix 1 + ix 1 + ix 1) = s.bytes.getD (p.val.toNat - 1 + 3) 0 := by
    rw [cu_eq, e3]; congr 1; omega
  generalize hL : s.bytes.drop (p.val.toNat - 1) = L
  have hlen : L.length = s.bytes.length - (p.val.toNat - 1) := by rw [← hL, List.length_drop]
  have hL0 : L.getD 0 0 = cu s p := by rw [← hL, getD_drop0, cu_eq, Nat.add_zero]
  have hL1 : L.getD 1 0 = cu s (p + ix 1) := by rw [← hL, getD_drop0, hB1]
  have hL2 : L.getD 2 0 = cu s (p + ix 1 + ix 1) := by rw [← hL, getD_drop0, hB2]
  have hL3 : L.getD 3 0 = cu s (p + ix 1 + ix 1 + ix 1) := by rw [← hL, getD_drop0, hB3]
  have q2 : decide (2 ≥ L.length) = decide ((p + ix 1 + ix 1).val > (ncodeunits s).val) := by
    rw [e2, ncu_val]; exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩
  have q3 : decide (3 ≥ L.length) = decide ((p + ix 1 + ix 1 + ix 1).val > (ncodeunits s).val) := by
    rw [e3, ncu_val]; exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩
  rw [iterate_eq s p h1 h2]
  by_cases hb : (!between (cu s p) 0x80 0xf7) = true
  · have hd : decAt L = ((cu s p).toUInt32 <<< 24, 1) := by
      simp only [decAt, hL0, hb, ↓reduceIte]
    rw [if_pos hb, hd]; exact ⟨_, rfl, by rw [e1]; rfl⟩
  rw [if_neg hb]
  rcases hr : iterateContinued s p ((cu s p).toUInt32 <<< 24) with ⟨u, j⟩
  unfold iterateContinued at hr
  dsimp only at hr
  split at hr
  next h0 =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    have hd : decAt L = ((cu s p).toUInt32 <<< 24, 1) := by
      simp only [decAt, hL0, hb, h0, Bool.false_eq_true, ↓reduceIte]
    rw [hd]; exact ⟨_, rfl, by rw [e1]; rfl⟩
  next h0 =>
  split at hr
  next hl =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    have q1 : 1 ≥ L.length := by rw [e1, ncu_val] at hl; omega
    have hd : decAt L = ((cu s p).toUInt32 <<< 24, 1) := by
      simp only [decAt, hL0, hb, h0, q1, Bool.false_eq_true, ↓reduceIte]
    rw [hd]; exact ⟨_, rfl, by rw [e1]; rfl⟩
  next hl =>
  have q1 : ¬ 1 ≥ L.length := by rw [e1, ncu_val] at hl; omega
  split at hr
  next hc =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    have hd : decAt L = ((cu s p).toUInt32 <<< 24, 1) := by
      simp only [decAt, hL0, hL1, hb, h0, q1, hc, Bool.false_eq_true, ↓reduceIte]
    rw [hd]; exact ⟨_, rfl, by rw [e1]; rfl⟩
  next hc =>
  split at hr
  next hl2 =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    have hd : decAt L = ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16, 2) := by
      simp only [decAt, hL0, hL1, hb, h0, q1, hc, q2, hl2, Bool.false_eq_true, ↓reduceIte]
    rw [hd]; exact ⟨_, rfl, by rw [e2]; rfl⟩
  next hl2 =>
  split at hr
  next hc2 =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    have hd : decAt L = ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16, 2) := by
      simp only [decAt, hL0, hL1, hL2, hb, h0, q1, hc, q2, hl2, hc2, Bool.false_eq_true, ↓reduceIte]
    rw [hd]; exact ⟨_, rfl, by rw [e2]; rfl⟩
  next hc2 =>
  split at hr
  next hl3 =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    have hd : decAt L = ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16 |||
        (cu s (p + ix 1 + ix 1)).toUInt32 <<< 8, 3) := by
      simp only [decAt, hL0, hL1, hL2, hb, h0, q1, hc, q2, hl2, hc2, q3, hl3, Bool.false_eq_true,
        ↓reduceIte]
    rw [hd]; exact ⟨_, rfl, by rw [e3]; rfl⟩
  next hl3 =>
  split at hr
  next hc3 =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    have hd : decAt L = ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16 |||
        (cu s (p + ix 1 + ix 1)).toUInt32 <<< 8, 3) := by
      simp only [decAt, hL0, hL1, hL2, hL3, hb, h0, q1, hc, q2, hl2, hc2, q3, hl3, hc3,
        Bool.false_eq_true, ↓reduceIte]
    rw [hd]; exact ⟨_, rfl, by rw [e3]; rfl⟩
  next hc3 =>
  simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
  have hd : decAt L = ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16 |||
      (cu s (p + ix 1 + ix 1)).toUInt32 <<< 8 ||| (cu s (p + ix 1 + ix 1 + ix 1)).toUInt32, 4) := by
    simp only [decAt, hL0, hL1, hL2, hL3, hb, h0, q1, hc, q2, hl2, hc2, q3, hl3, hc3,
      Bool.false_eq_true, ↓reduceIte]
  rw [hd]; exact ⟨_, rfl, by rw [e4]; rfl⟩

/-! ## The byte shapes of the chars of a string -/

/-- The four byte shapes `decAt` produces: one byte, or a lead byte `0xc0-0xf7`
followed by one to three continuation bytes, as many as the lead allows at most. -/
def Shape (c : UInt32) : Prop :=
  (∃ b0 : UInt8, c = b0.toUInt32 <<< 24) ∨
  (∃ b0 b1 : UInt8, 192 ≤ b0.toNat ∧ b0.toNat ≤ 247 ∧ 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧
    c = b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) ∨
  (∃ b0 b1 b2 : UInt8, 224 ≤ b0.toNat ∧ b0.toNat ≤ 247 ∧ 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧
    128 ≤ b2.toNat ∧ b2.toNat < 192 ∧
    c = b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) ∨
  (∃ b0 b1 b2 b3 : UInt8, 240 ≤ b0.toNat ∧ b0.toNat ≤ 247 ∧ 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧
    128 ≤ b2.toNat ∧ b2.toNat < 192 ∧ 128 ≤ b3.toNat ∧ b3.toNat < 192 ∧
    c = b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32)

theorem not_lt_c0 (b0 : UInt8) (h : ¬ b0.toUInt32 <<< 24 < 0xc0000000) : 192 ≤ b0.toNat := by
  rw [UInt32.lt_iff_toNat_lt, v1] at h
  have : (0xc0000000 : UInt32).toNat = 3221225472 := rfl
  rw [this] at h; omega

theorem not_lt_e0 (b0 b1 : UInt8) (h : ¬ (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) < 0xe0000000) :
    224 ≤ b0.toNat := by
  have := b1.toNat_lt
  rw [UInt32.lt_iff_toNat_lt, v2] at h
  have : (0xe0000000 : UInt32).toNat = 3758096384 := rfl
  omega

theorem not_lt_f0 (b0 b1 b2 : UInt8)
    (h : ¬ (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) < 0xf0000000) :
    240 ≤ b0.toNat := by
  have := b1.toNat_lt; have := b2.toNat_lt
  rw [UInt32.lt_iff_toNat_lt, v3] at h
  have : (0xf0000000 : UInt32).toNat = 4026531840 := rfl
  omega

theorem between_le (b : UInt8) (h : ¬ (!between b 0x80 0xf7) = true) : b.toNat ≤ 247 := by
  have hb : between b 0x80 0xf7 = true := by simpa using h
  rw [between_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
  exact hb.2

theorem cont_of (b : UInt8) (h : ¬ (!isCont b) = true) : 128 ≤ b.toNat ∧ b.toNat < 192 := by
  rw [isCont_eq] at h; simpa using h

theorem decAt_shape (L : List UInt8) : Shape (decAt L).1 ∧ 1 ≤ (decAt L).2 ∧
    (L ≠ [] → (decAt L).2 ≤ L.length) := by
  have one : Shape ((L.getD 0 0).toUInt32 <<< 24) := .inl ⟨_, rfl⟩
  have nz : L ≠ [] → 1 ≤ L.length := fun h => by
    cases L with
    | nil => exact absurd rfl h
    | cons _ _ => simp
  unfold decAt
  dsimp only
  split
  · exact ⟨one, Nat.le_refl _, nz⟩
  next hb =>
  split
  · exact ⟨one, Nat.le_refl _, nz⟩
  next h0 =>
  split
  · exact ⟨one, Nat.le_refl _, nz⟩
  next hl =>
  split
  · exact ⟨one, Nat.le_refl _, nz⟩
  next hc =>
  have b0a := not_lt_c0 _ h0
  have b0b := between_le _ hb
  have c1 := cont_of _ hc
  split
  · exact ⟨.inr (.inl ⟨_, _, b0a, b0b, c1.1, c1.2, rfl⟩), by omega, fun _ => by omega⟩
  next hl2 =>
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hl2
  have b0c := not_lt_e0 _ _ hl2.2
  split
  · exact ⟨.inr (.inl ⟨_, _, b0a, b0b, c1.1, c1.2, rfl⟩), by omega, fun _ => by omega⟩
  next hc2 =>
  have c2 := cont_of _ hc2
  split
  · exact ⟨.inr (.inr (.inl ⟨_, _, _, b0c, b0b, c1.1, c1.2, c2.1, c2.2, rfl⟩)), by omega,
      fun _ => by omega⟩
  next hl3 =>
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hl3
  have b0d := not_lt_f0 _ _ _ hl3.2
  split
  · exact ⟨.inr (.inr (.inl ⟨_, _, _, b0c, b0b, c1.1, c1.2, c2.1, c2.2, rfl⟩)), by omega,
      fun _ => by omega⟩
  next hc3 =>
  have c3 := cont_of _ hc3
  exact ⟨.inr (.inr (.inr ⟨_, _, _, _, b0d, b0b, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, rfl⟩)),
    by omega, fun _ => by omega⟩

theorem collect_shape (s : JStr) (k : Nat) : ∀ (p : JInt64), 1 ≤ p.val → p.val ≤ s.bytes.length + 1 →
    ∀ c ∈ (collectFrom s k p).map (·.1), Shape c := by
  induction k with
  | zero => intro p _ _ c hc; rw [collectFrom_eq_iterList] at hc; simp [iterList] at hc
  | succ k ih =>
    intro p h1 h2 c hc
    by_cases hend : p.val = s.bytes.length + 1
    · rw [collectFrom_none s k p (iterate_end s p hend)] at hc; simp at hc
    · obtain ⟨j, hit, hj⟩ := iterate_dec s p h1 (by omega)
      rw [collectFrom_some s k p _ j hit] at hc
      have hsh := decAt_shape (s.bytes.drop (p.val.toNat - 1))
      have hne : s.bytes.drop (p.val.toNat - 1) ≠ [] := by
        intro h; have := congrArg List.length h; simp at this; omega
      have hle := hsh.2.2 hne
      rw [List.length_drop] at hle
      simp only [List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hsh.1
      · exact ih j (by omega) (by omega) c hc

theorem chars_shape (s : JStr) : ∀ c ∈ chars s, Shape c := by
  have e1 : (ix 1).val = 1 := rfl
  exact collect_shape s _ (ix 1) (by rw [e1]; decide) (by rw [e1]; omega)

/-! ## Strings of complete chars iterate back to their chars -/

/-- A char whose bytes `iterate` reads back as that char whatever follows: an
ASCII byte, or a lead byte followed by exactly the number of continuation bytes
it announces. -/
def Complete (c : UInt32) : Prop :=
  (∃ b0 : UInt8, b0.toNat < 128 ∧ c = b0.toUInt32 <<< 24) ∨
  (∃ b0 b1 : UInt8, 192 ≤ b0.toNat ∧ b0.toNat < 224 ∧ 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧
    c = b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) ∨
  (∃ b0 b1 b2 : UInt8, 224 ≤ b0.toNat ∧ b0.toNat < 240 ∧ 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧
    128 ≤ b2.toNat ∧ b2.toNat < 192 ∧
    c = b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) ∨
  (∃ b0 b1 b2 b3 : UInt8, 240 ≤ b0.toNat ∧ b0.toNat ≤ 247 ∧ 128 ≤ b1.toNat ∧ b1.toNat < 192 ∧
    128 ≤ b2.toNat ∧ b2.toNat < 192 ∧ 128 ≤ b3.toNat ∧ b3.toNat < 192 ∧
    c = b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32)

theorem lt_c0 (b0 : UInt8) : (b0.toUInt32 <<< 24 < 0xc0000000) ↔ b0.toNat < 192 := by
  rw [UInt32.lt_iff_toNat_lt, v1]
  have : (0xc0000000 : UInt32).toNat = 3221225472 := rfl
  rw [this]; omega

theorem lt_e0 (b0 b1 : UInt8) :
    ((b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) < 0xe0000000) ↔ b0.toNat < 224 := by
  have := b1.toNat_lt
  rw [UInt32.lt_iff_toNat_lt, v2]
  have : (0xe0000000 : UInt32).toNat = 3758096384 := rfl
  rw [this]; omega

theorem lt_f0 (b0 b1 b2 : UInt8) :
    ((b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) < 0xf0000000) ↔
      b0.toNat < 240 := by
  have := b1.toNat_lt; have := b2.toNat_lt
  rw [UInt32.lt_iff_toNat_lt, v3]
  have : (0xf0000000 : UInt32).toNat = 4026531840 := rfl
  rw [this]; omega

theorem nb_true (b : UInt8) (h : b.toNat < 128) : (!between b 0x80 0xf7) = true := by
  rw [between_eq, decide_eq_false (show ¬ ((0x80 : UInt8).toNat ≤ b.toNat) by
    show ¬ (128 ≤ b.toNat); omega)]
  rfl

theorem nb_false (b : UInt8) (h1 : 128 ≤ b.toNat) (h2 : b.toNat ≤ 247) :
    (!between b 0x80 0xf7) = false := by
  rw [between_eq, decide_eq_true (show (0x80 : UInt8).toNat ≤ b.toNat from h1),
    decide_eq_true (show b.toNat ≤ (0xf7 : UInt8).toNat from h2)]
  rfl

theorem cont_f (b : UInt8) (h1 : 128 ≤ b.toNat) (h2 : b.toNat < 192) : (!isCont b) = false := by
  rw [isCont_eq, decide_eq_true (show 128 ≤ b.toNat ∧ b.toNat < 192 from ⟨h1, h2⟩)]
  rfl

theorem decAt1 (b0 : UInt8) (h : b0.toNat < 128) (rest : List UInt8) :
    decAt (b0 :: rest) = (b0.toUInt32 <<< 24, 1) := by
  have e0 := nb_true b0 h
  unfold decAt
  simp only [List.getD_cons_zero, e0, ↓reduceIte]

theorem decAt2 (b0 b1 : UInt8) (h0 : 192 ≤ b0.toNat) (h0' : b0.toNat < 224) (h1 : 128 ≤ b1.toNat)
    (h1' : b1.toNat < 192) (rest : List UInt8) :
    decAt (b0 :: b1 :: rest) = (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16, 2) := by
  have e0 := nb_false b0 (by omega) (by omega)
  have e1 : ¬ (b0.toUInt32 <<< 24 < 0xc0000000) := by rw [lt_c0]; omega
  have e2 : ¬ (1 ≥ (b0 :: b1 :: rest).length) := by simp
  have e3 := cont_f b1 h1 h1'
  have e4 : (decide (2 ≥ (b0 :: b1 :: rest).length) ||
      decide (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 < 0xe0000000)) = true := by
    rw [decide_eq_true ((lt_e0 b0 b1).mpr h0'), Bool.or_true]
  unfold decAt
  simp only [List.getD_cons_zero, List.getD_cons_succ, e0, e1, e2, e3, e4, Bool.false_eq_true,
    ↓reduceIte]

theorem decAt3 (b0 b1 b2 : UInt8) (h0 : 224 ≤ b0.toNat) (h0' : b0.toNat < 240)
    (h1 : 128 ≤ b1.toNat) (h1' : b1.toNat < 192) (h2 : 128 ≤ b2.toNat) (h2' : b2.toNat < 192)
    (rest : List UInt8) :
    decAt (b0 :: b1 :: b2 :: rest) =
      (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8, 3) := by
  have e0 := nb_false b0 (by omega) (by omega)
  have e1 : ¬ (b0.toUInt32 <<< 24 < 0xc0000000) := by rw [lt_c0]; omega
  have e2 : ¬ (1 ≥ (b0 :: b1 :: b2 :: rest).length) := by simp
  have e3 := cont_f b1 h1 h1'
  have e4 : (decide (2 ≥ (b0 :: b1 :: b2 :: rest).length) ||
      decide (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 < 0xe0000000)) = false := by
    rw [decide_eq_false (by simp), decide_eq_false (by rw [lt_e0]; omega)]; rfl
  have e5 := cont_f b2 h2 h2'
  have e6 : (decide (3 ≥ (b0 :: b1 :: b2 :: rest).length) ||
      decide (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 < 0xf0000000)) =
      true := by
    rw [decide_eq_true ((lt_f0 b0 b1 b2).mpr h0'), Bool.or_true]
  unfold decAt
  simp only [List.getD_cons_zero, List.getD_cons_succ, e0, e1, e2, e3, e4, e5, e6,
    Bool.false_eq_true, ↓reduceIte]

theorem decAt4 (b0 b1 b2 b3 : UInt8) (h0 : 240 ≤ b0.toNat) (h0' : b0.toNat ≤ 247)
    (h1 : 128 ≤ b1.toNat) (h1' : b1.toNat < 192) (h2 : 128 ≤ b2.toNat) (h2' : b2.toNat < 192)
    (h3 : 128 ≤ b3.toNat) (h3' : b3.toNat < 192) (rest : List UInt8) :
    decAt (b0 :: b1 :: b2 :: b3 :: rest) =
      (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32, 4) := by
  have e0 := nb_false b0 (by omega) (by omega)
  have e1 : ¬ (b0.toUInt32 <<< 24 < 0xc0000000) := by rw [lt_c0]; omega
  have e2 : ¬ (1 ≥ (b0 :: b1 :: b2 :: b3 :: rest).length) := by simp
  have e3 := cont_f b1 h1 h1'
  have e4 : (decide (2 ≥ (b0 :: b1 :: b2 :: b3 :: rest).length) ||
      decide (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 < 0xe0000000)) = false := by
    rw [decide_eq_false (by simp), decide_eq_false (by rw [lt_e0]; omega)]; rfl
  have e5 := cont_f b2 h2 h2'
  have e6 : (decide (3 ≥ (b0 :: b1 :: b2 :: b3 :: rest).length) ||
      decide (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 < 0xf0000000)) =
      false := by
    rw [decide_eq_false (by simp), decide_eq_false (by rw [lt_f0]; omega)]; rfl
  have e7 := cont_f b3 h3 h3'
  unfold decAt
  simp only [List.getD_cons_zero, List.getD_cons_succ, e0, e1, e2, e3, e4, e5, e6, e7,
    Bool.false_eq_true, ↓reduceIte]

theorem decAt_complete (c : UInt32) (hc : Complete c) (rest : List UInt8) :
    decAt (writeChar c ++ rest) = (c, (writeChar c).length) := by
  rcases hc with ⟨b0, h0, rfl⟩ | ⟨b0, b1, h0, h0', h1, h1', rfl⟩ |
    ⟨b0, b1, b2, h0, h0', h1, h1', h2, h2', rfl⟩ |
    ⟨b0, b1, b2, b3, h0, h0', h1, h1', h2, h2', h3, h3', rfl⟩
  · rw [wc1]; exact decAt1 b0 h0 rest
  · rw [wc2 _ _ h1]; exact decAt2 b0 b1 h0 h0' h1 h1' rest
  · rw [wc3 _ _ _ h1 h2]; exact decAt3 b0 b1 b2 h0 h0' h1 h1' h2 h2' rest
  · rw [wc4 _ _ _ _ h1 h2 h3]; exact decAt4 b0 b1 b2 b3 h0 h0' h1 h1' h2 h2' h3 h3' rest

theorem wc_cons (c : UInt32) : ∃ b bs, writeChar c = b :: bs := ⟨_, _, rfl⟩

theorem wc_ne (c : UInt32) : writeChar c ≠ [] := by
  obtain ⟨b, bs, h⟩ := wc_cons c
  rw [h]; exact List.cons_ne_nil _ _

theorem collect_complete (s : JStr) (k : Nat) : ∀ (p : JInt64) (cs : List UInt32), 1 ≤ p.val →
    p.val ≤ s.bytes.length + 1 → s.bytes.length + 1 - p.val < k →
    s.bytes.drop (p.val.toNat - 1) = cs.flatMap writeChar → (∀ c ∈ cs, Complete c) →
    (collectFrom s k p).map (·.1) = cs := by
  induction k with
  | zero => intro p _ _ _ hk; omega
  | succ k ih =>
    intro p cs h1 h2 hk hd hc
    by_cases hend : p.val = s.bytes.length + 1
    · rw [collectFrom_none s k p (iterate_end s p hend)]
      have h0 : s.bytes.drop (p.val.toNat - 1) = [] := List.drop_eq_nil_of_le (by omega)
      rw [h0] at hd
      cases cs with
      | nil => rfl
      | cons c cs =>
        rw [List.flatMap_cons] at hd
        exact absurd (List.append_eq_nil_iff.mp hd.symm).1 (wc_ne c)
    · obtain ⟨j, hit, hj⟩ := iterate_dec s p h1 (by omega)
      cases cs with
      | nil =>
        exfalso
        have := congrArg List.length hd
        simp at this; omega
      | cons c cs =>
        have hl := congrArg List.length hd
        rw [List.length_drop, List.flatMap_cons, List.length_append] at hl
        have hlen1 : 1 ≤ (writeChar c).length := by
          obtain ⟨b, bs, h⟩ := wc_cons c; rw [h]; simp
        rw [hd, List.flatMap_cons, decAt_complete c (hc c (by simp)) _] at hit hj
        have hj' : j.val = p.val + (writeChar c).length := hj
        rw [collectFrom_some s k p _ j hit]
        simp only [List.map_cons]
        refine congr (congrArg List.cons rfl) (ih j cs (by omega) (by omega) (by omega) ?_
          (fun x hx => hc x (by simp [hx])))
        have hq : j.val.toNat - 1 = (p.val.toNat - 1) + (writeChar c).length := by omega
        rw [hq, ← dd, hd, List.flatMap_cons, List.drop_left]

theorem chars_of_complete (s : JStr) (cs : List UInt32) (hd : s.bytes = cs.flatMap writeChar)
    (hc : ∀ c ∈ cs, Complete c) : chars s = cs := by
  have e1 : (ix 1).val = 1 := rfl
  have hs := ncu_small s
  exact collect_complete s (s.bytes.length + 1) (ix 1) cs (by rw [e1]; decide) (by rw [e1]; omega)
    (by rw [e1]; omega) (by rw [e1]; simpa using hd) hc

/-! ## Hex digits -/

/-- The `Char` of an ASCII byte. -/
def acB (b : UInt8) : UInt32 := b.toUInt32 <<< 24

theorem acB5c : acB 0x5c = ac 0x5c := by decide

theorem u8_of (b : UInt8) : b.toNat.toUInt8 = b := UInt8.toNat_inj.mp (by simp)

theorem acB_inj {a b : UInt8} (h : acB a = acB b) : a = b := by
  have := congrArg UInt32.toNat h
  simp only [acB, v1] at this
  exact UInt8.toNat_inj.mp (by omega)

theorem flat_acB : ∀ bs : List UInt8, (bs.map acB).flatMap writeChar = bs
  | [] => rfl
  | b :: bs => by
    rw [List.map_cons, List.flatMap_cons, flat_acB bs]
    show writeChar (b.toUInt32 <<< 24) ++ bs = b :: bs
    rw [wc1]; rfl

theorem complete_ascii (bs : List UInt8) (h : asciiOut bs = true) : ∀ x ∈ bs.map acB, Complete x := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  simp only [asciiOut, List.all_eq_true, decide_eq_true_eq] at h
  have h1 := h b hb
  rw [UInt8.lt_iff_toNat_lt] at h1
  exact .inl ⟨b, h1, rfl⟩

/-- The digit values `hexStr x` prints for a width `W`, most significant first. -/
def hexDs (x W : Nat) : List Nat := (List.range W).reverse.map (fun i => x / 16 ^ i % 16)

/-- The value of a list of hex digits read left to right onto `n`. -/
def hfold (n : Nat) (ds : List Nat) : Nat := ds.foldl (fun a d => a * 16 + d) n

theorem hexStr_eq (x p : Nat) : hexStr x p = (hexDs x (max p (nibbles 16 x))).map hexDigit := by
  simp only [hexStr, hexDs, List.map_map]; rfl

theorem hexStr_len (x p : Nat) : (hexStr x p).length = max p (nibbles 16 x) := by
  simp [hexStr]

theorem hexDs_succ (x W : Nat) : hexDs x (W + 1) = (x / 16 ^ W % 16) :: hexDs x W := by
  simp [hexDs, List.range_succ]

theorem hexDs_length (x W : Nat) : (hexDs x W).length = W := by simp [hexDs]

theorem hexDs_lt (x W : Nat) : ∀ d ∈ hexDs x W, d < 16 := by
  intro d hd
  simp only [hexDs, List.mem_map] at hd
  obtain ⟨i, _, rfl⟩ := hd
  exact Nat.mod_lt _ (by decide)

theorem hexDs_fold (x : Nat) : ∀ W n, hfold n (hexDs x W) = n * 16 ^ W + x % 16 ^ W
  | 0, n => by simp [hfold, hexDs, Nat.mod_one]
  | W + 1, n => by
    rw [hexDs_succ, hfold, List.foldl_cons, ← hfold, hexDs_fold x W, Nat.pow_succ, Nat.mod_mul]
    generalize 16 ^ W = P
    generalize x / P % 16 = q
    generalize x % P = r
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 16 P, Nat.mul_comm q P]
    omega

theorem nibbles_lt : ∀ k x, x < 16 ^ k → x < 16 ^ nibbles k x
  | 0, x, h => by unfold nibbles; exact h
  | k + 1, x, h => by
    unfold nibbles
    split
    · simp_all
    · have h1 : x / 16 < 16 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h
      have := nibbles_lt k (x / 16) h1
      rw [Nat.add_comm, Nat.pow_succ]
      exact (Nat.div_lt_iff_lt_mul (by decide)).mp this

theorem nibbles_le : ∀ k x j, x < 16 ^ j → nibbles k x ≤ j
  | 0, _, _, _ => by unfold nibbles; omega
  | k + 1, x, j, h => by
    unfold nibbles
    split
    · omega
    · rename_i hx
      cases j with
      | zero => simp at h; omega
      | succ j =>
        have h1 : x / 16 < 16 ^ j := by
          rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h
        have := nibbles_le k (x / 16) j h1
        omega

theorem hexStr_val (x p : Nat) (hx : x < 16 ^ 16) : hfold 0 (hexDs x (max p (nibbles 16 x))) = x := by
  rw [hexDs_fold]
  have h1 := nibbles_lt 16 x hx
  have h2 : 16 ^ nibbles 16 x ≤ 16 ^ max p (nibbles 16 x) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
  rw [Nat.mod_eq_of_lt (by omega)]
  simp

theorem hexVal_tab : ∀ d : Fin 16, hexVal (acB (hexDigit d.val)) = some d.val := by decide +kernel

theorem hexVal_digit (d : Nat) (h : d < 16) : hexVal (acB (hexDigit d)) = some d := hexVal_tab ⟨d, h⟩

theorem hexVal_none (c : UInt32) (h : isxdigit c = false) : hexVal c = none := by
  unfold isxdigit at h
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold hexVal
  rw [if_neg (by rw [h1]; decide), if_neg (by rw [h2]; decide), if_neg (by rw [h3]; decide)]

theorem asc_x : asc ['\\', 'x'] = [0x5c, 0x78] := by decide
theorem asc_u : asc ['\\', 'u'] = [0x5c, 0x75] := by decide
theorem asc_U : asc ['\\', 'U'] = [0x5c, 0x55] := by decide

theorem piece_hex (e : UInt8) (x p : Nat) (T : List UInt32) :
    ([0x5c, e] ++ hexStr x p).map acB ++ T =
      ac 0x5c :: acB e :: ((hexDs x (max p (nibbles 16 x))).map (fun d => acB (hexDigit d)) ++ T) := by
  rw [hexStr_eq, List.map_append, List.map_map]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, acB5c]
  rfl

/-- `\x` and two hex digits for the byte `b`. -/
def hx (b : UInt8) : List UInt8 := asc ['\\', 'x'] ++ hexStr b.toNat 2

theorem nib_byte (b : UInt8) : max 2 (nibbles 16 b.toNat) = 2 :=
  Nat.max_eq_left (nibbles_le 16 b.toNat 2 (by have := b.toNat_lt; show b.toNat < 256; omega))

theorem hx_map (b : UInt8) : (hx b).map acB =
    ac 0x5c :: acB 0x78 :: (hexDs b.toNat 2).map (fun d => acB (hexDigit d)) := by
  have := piece_hex 0x78 b.toNat 2 []
  rw [nib_byte, List.append_nil, List.append_nil] at this
  rw [hx, asc_x]; exact this

theorem hx_len (b : UInt8) : (hx b).length = 4 := by
  rw [hx, asc_x, List.length_append, hexStr_len, nib_byte]; rfl

theorem flatMap_hx_len : ∀ bs : List UInt8, (bs.flatMap hx).length = 4 * bs.length
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, List.length_append, hx_len, flatMap_hx_len bs, List.length_cons]; omega

theorem hexBytes_eq : ∀ (k : Nat) (u : UInt32), hexBytesAux k u = (writeCharAux k u).flatMap hx
  | 0, _ => rfl
  | k + 1, u => by
    rw [hexBytesAux, writeCharAux, List.flatMap_cons]
    by_cases h : u >>> 8 = 0
    · rw [if_pos h, if_pos h]; simp [hx]
    · rw [if_neg h, if_neg h, hexBytes_eq k]; simp [hx]

/-! ## Steps of the `unescape_string` loop -/

/-- The value written for a `\x` (`m = 2`), `\u` (`m = 4`) or `\U` (`m = 8`) escape
with value `n`. -/
def hexOut (m n : Nat) : List UInt8 := if m = 2 then [n.toUInt8] else writeChar (charOfCp n)

theorem uloop_nil (f : Nat) : unescLoop [] f [] = .ok [] := by cases f <;> rfl

theorem uloop_raw (c : UInt32) (L : List UInt32) (f : Nat) (hc : c ≠ ac 0x5c) :
    unescLoop [] (f + 1) (c :: L) = (fun r => writeChar c ++ r) <$> unescLoop [] f L := by
  cases L with
  | nil => rw [unescLoop, if_neg (by simp [hc])]
  | cons e L => rw [unescLoop, if_neg (by simp [hc])]

theorem U_simple (e o : UInt32) (L : List UInt32) (f : Nat)
    (h1 : (e = ac 0x78 || e = ac 0x75 || e = ac 0x55) = false)
    (h2 : (decide (ac 0x30 ≤ e) && decide (e ≤ ac 0x37)) = false)
    (h3 : unescSimple e = some o) :
    unescLoop [] (f + 1) (ac 0x5c :: e :: L) = (fun r => writeChar o ++ r) <$> unescLoop [] f L := by
  rw [unescLoop, if_pos (by simp)]
  rw [if_neg (by simp), if_neg (by rw [h1]; decide), if_neg (by rw [h2]; decide), h3]

theorem U_oct0 (L : List UInt32) (f : Nat)
    (hla : ∀ x, L.head? = some x → (decide (ac 0x30 ≤ x) && decide (x ≤ ac 0x37)) = false) :
    unescLoop [] (f + 1) (ac 0x5c :: ac 0x30 :: L) = (fun r => [0] ++ r) <$> unescLoop [] f L := by
  rw [unescLoop, if_pos (by simp)]
  rw [if_neg (by simp), if_neg (by decide), if_pos (by decide)]
  have hc : (cpOf (ac 0x30)).toNat - 0x30 = 0 := by decide
  rw [hc]
  have ho : unescOct 3 1 0 L = (0, L) := by
    cases L with
    | nil => rfl
    | cons x L =>
      rw [unescOct, if_pos (by omega)]
      rw [if_neg (by rw [hla x rfl]; decide)]
  rw [ho]
  rfl

theorem unescHex_digits (m : Nat) (L : List UInt32) : ∀ (ds : List Nat) (k n F : Nat),
    k + ds.length ≤ m → ds.length < F → (∀ d ∈ ds, d < 16) →
    unescHex m F k n (ds.map (fun d => acB (hexDigit d)) ++ L) =
      unescHex m (F - ds.length) (k + ds.length) (hfold n ds) L
  | [], k, n, F, _, _, _ => by simp [hfold]
  | d :: ds, k, n, F, h1, h2, h3 => by
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at h2; omega⟩
    simp only [List.map_cons, List.cons_append]
    rw [unescHex, if_pos (by simp at h1; omega)]
    rw [hexVal_digit d (h3 d (by simp))]
    dsimp only
    rw [unescHex_digits m L ds (k + 1) (n * 16 + d) F' (by simp at h1; omega) (by simp at h2; omega)
      (fun x hx => h3 x (by simp [hx]))]
    simp only [List.length_cons]
    rw [show F' + 1 - (ds.length + 1) = F' - ds.length by omega,
      show k + (ds.length + 1) = k + 1 + ds.length by omega]
    rfl

theorem unescHex_stop (m F k n : Nat) (L : List UInt32)
    (h : m < k + 1 ∨ ∀ x, L.head? = some x → hexVal x = none) :
    unescHex m (F + 1) k n L = (k + 1, n, L) := by
  cases L with
  | nil => rw [unescHex]; split <;> rfl
  | cons x L =>
    rw [unescHex]
    by_cases hk : k + 1 ≤ m
    · rw [if_pos hk]
      rcases h with h | h
      · omega
      · rw [h x rfl]
    · rw [if_neg hk]

theorem U_hex (e : UInt8) (m : Nat)
    (hm : (e = 0x78 ∧ m = 2) ∨ (e = 0x75 ∧ m = 4) ∨ (e = 0x55 ∧ m = 8))
    (ds : List Nat) (hd : ∀ x ∈ ds, x < 16) (h1 : 1 ≤ ds.length) (h2 : ds.length ≤ m)
    (L : List UInt32) (hla : ds.length < m → ∀ x, L.head? = some x → hexVal x = none)
    (hn : hfold 0 ds ≤ 0x10ffff) (f : Nat) :
    unescLoop [] (f + 1) (ac 0x5c :: acB e :: (ds.map (fun d => acB (hexDigit d)) ++ L)) =
      (fun r => hexOut m (hfold 0 ds) ++ r) <$> unescLoop [] f L := by
  have hu : unescHex m (m + 1) 0 0 (ds.map (fun d => acB (hexDigit d)) ++ L) =
      (ds.length + 1, hfold 0 ds, L) := by
    rw [unescHex_digits m L ds 0 0 (m + 1) (by omega) (by omega) hd,
      show m + 1 - ds.length = (m - ds.length) + 1 by omega, unescHex_stop]
    · simp
    · by_cases hl : ds.length < m
      · exact .inr (hla hl)
      · exact .inl (by omega)
  have hk : ¬ ((decide (ds.length + 1 = 1) || decide (hfold 0 ds > 0x10ffff)) = true) := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [unescLoop, if_pos (by simp)]
    rw [if_neg (by simp), if_pos (by decide)]
    dsimp only
    rw [if_pos (show acB 0x78 = ac 0x78 by decide), hu]
    dsimp only
    rw [if_neg hk, if_pos rfl]
    rfl
  · rw [unescLoop, if_pos (by simp)]
    rw [if_neg (by simp), if_pos (by decide)]
    dsimp only
    rw [if_neg (show ¬ acB 0x75 = ac 0x78 by decide),
      if_pos (show acB 0x75 = ac 0x75 by decide), hu]
    dsimp only
    rw [if_neg hk, if_neg (by decide)]
    rfl
  · rw [unescLoop, if_pos (by simp)]
    rw [if_neg (by simp), if_pos (by decide)]
    dsimp only
    rw [if_neg (show ¬ acB 0x55 = ac 0x78 by decide),
      if_neg (show ¬ acB 0x55 = ac 0x75 by decide), hu]
    dsimp only
    rw [if_neg hk, if_neg (by decide)]
    rfl

theorem hexOut2 (b : UInt8) : hexOut 2 b.toNat = [b] := by
  unfold hexOut; rw [if_pos rfl, u8_of]

theorem U_hx (b : UInt8) (T : List UInt32) (f : Nat) :
    unescLoop [] (f + 1) ((hx b).map acB ++ T) = (fun r => [b] ++ r) <$> unescLoop [] f T := by
  have hval : hfold 0 (hexDs b.toNat 2) = b.toNat := by
    have := hexStr_val b.toNat 2 (by have := b.toNat_lt; show b.toNat < 18446744073709551616; omega)
    rwa [nib_byte] at this
  rw [hx_map, List.cons_append, List.cons_append,
    U_hex 0x78 2 (.inl ⟨rfl, rfl⟩) (hexDs b.toNat 2) (hexDs_lt _ _) (by rw [hexDs_length]; omega)
      (by rw [hexDs_length]; exact Nat.le_refl _) T (fun hl => absurd hl (by rw [hexDs_length]; omega))
      (by rw [hval]; have := b.toNat_lt; omega) f, hval, hexOut2]

theorem U_hexbytes (T : List UInt32) : ∀ (bs : List UInt8) (f : Nat),
    unescLoop [] (f + bs.length) ((bs.flatMap hx).map acB ++ T) =
      (fun r => bs ++ r) <$> unescLoop [] f T
  | [], f => by
    show unescLoop [] f T = _
    cases unescLoop [] f T <;> rfl
  | b :: bs, f => by
    rw [List.flatMap_cons, List.map_append, List.append_assoc, List.length_cons, ← Nat.add_assoc,
      U_hx, U_hexbytes T bs f]
    cases unescLoop [] f T <;> rfl

/-! ## The escaped pieces -/

/-- `escape_nul(c)`'s test on the next char. -/
def octB : Option UInt32 → Bool
  | some c => decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x37)
  | none => false

/-- `escChar` with the default arguments, with `isprint(c)`, `escape_nul`'s test and
`need_full_hex` on the next char passed as booleans. -/
def escCharP (p z h : Bool) (c : UInt32) : List UInt8 :=
  if c ∈ [ac 0x22] then 0x5c :: writeChar c
  else if c ∈ ([] : List UInt32) then writeChar c
  else if isasciiChar c then
    if c = ac 0 then (if z then asc ['\\', 'x', '0', '0'] else asc ['\\', '0'])
    else if c = ac 0x1b then asc ['\\', 'e']
    else if c = ac 0x5c then asc ['\\', '\\']
    else if decide (ac 0x07 ≤ c) && decide (c ≤ ac 0x0d) then
      [0x5c, (asc ['a', 'b', 't', 'n', 'v', 'f', 'r']).getD ((cpOf c).toNat - 7) 0]
    else if p then writeChar c
    else asc ['\\', 'x'] ++ hexStr (cpOf c).toNat 2
  else if !isoverlong c && !ismalformed c then
    if !false && p then writeChar c
    else if c ≤ ac 0x7f then asc ['\\', 'x'] ++ hexStr (cpOf c).toNat 2
    else if c ≤ 0xefbfbf00 then
      asc ['\\', 'u'] ++ hexStr (cpOf c).toNat (if false || h then 4 else 2)
    else asc ['\\', 'U'] ++ hexStr (cpOf c).toNat (if false || h then 8 else 4)
  else hexBytesAux 4 (bswap32 c)

theorem escChar_eq (d : UData) (c : UInt32) (nxt : Option UInt32) :
    escChar d [ac 0x22] [] false false c nxt =
      escCharP (isprint d c) (octB nxt) (needFullHex nxt) c := by
  cases nxt <;> rfl

theorem not_q (c : UInt32) (hasc : isasciiChar c = false) : ¬ c ∈ [ac 0x22] := by
  intro hm
  simp only [List.mem_singleton] at hm
  rw [hm] at hasc
  exact absurd hasc (by decide)

theorem escP_X (p z h : Bool) (c : UInt32) (hasc : isasciiChar c = false)
    (hwf : (!isoverlong c && !ismalformed c) = false) :
    escCharP p z h c = hexBytesAux 4 (bswap32 c) := by
  unfold escCharP
  rw [if_neg (not_q c hasc), if_neg (by simp), if_neg (by rw [hasc]; decide),
    if_neg (by rw [hwf]; decide)]

theorem escP_raw (z h : Bool) (c : UInt32) (hasc : isasciiChar c = false)
    (hwf : (!isoverlong c && !ismalformed c) = true) : escCharP true z h c = writeChar c := by
  unfold escCharP
  rw [if_neg (not_q c hasc), if_neg (by simp), if_neg (by rw [hasc]; decide), if_pos hwf, if_pos (show (!false && true) = true from rfl)]

theorem escP_u (z h : Bool) (c : UInt32) (hasc : isasciiChar c = false)
    (hwf : (!isoverlong c && !ismalformed c) = true) (h7f : ¬ c ≤ ac 0x7f) (hU : c ≤ 0xefbfbf00) :
    escCharP false z h c = asc ['\\', 'u'] ++ hexStr (cpOf c).toNat (if false || h then 4 else 2) := by
  unfold escCharP
  rw [if_neg (not_q c hasc), if_neg (by simp), if_neg (by rw [hasc]; decide), if_pos hwf,
    if_neg (by decide), if_neg h7f, if_pos hU]

theorem escP_U (z h : Bool) (c : UInt32) (hasc : isasciiChar c = false)
    (hwf : (!isoverlong c && !ismalformed c) = true) (h7f : ¬ c ≤ ac 0x7f) (hU : ¬ c ≤ 0xefbfbf00) :
    escCharP false z h c = asc ['\\', 'U'] ++ hexStr (cpOf c).toNat (if false || h then 8 else 4) := by
  unfold escCharP
  rw [if_neg (not_q c hasc), if_neg (by simp), if_neg (by rw [hasc]; decide), if_pos hwf,
    if_neg (by decide), if_neg h7f, if_neg hU]

/-- The chars printed raw: well-formed, non-overlong, non-ASCII and printable. -/
def rawC (d : UData) (c : UInt32) : Bool :=
  !isasciiChar c && (!isoverlong c && !ismalformed c) && isprint d c

/-- The chars of the piece `escape_string` prints for `c` (followed by `nxt`):
`c` itself when printed raw, otherwise the ASCII bytes of its escape. -/
def escCharC (d : UData) (c : UInt32) (nxt : Option UInt32) : List UInt32 :=
  if rawC d c then [c] else (escChar d [ac 0x22] [] false false c nxt).map acB

/-- The chars of the escaped string, piece by piece. -/
def escLoopC (d : UData) : List UInt32 → List UInt32
  | [] => []
  | c :: rest => escCharC d c rest.head? ++ escLoopC d rest

theorem rawC_spec {d : UData} {c : UInt32} (h : rawC d c = true) :
    isasciiChar c = false ∧ (!isoverlong c && !ismalformed c) = true ∧ isprint d c = true := by
  unfold rawC at h
  revert h
  generalize isasciiChar c = a
  generalize (!isoverlong c && !ismalformed c) = w
  generalize isprint d c = p
  cases a <;> cases w <;> cases p <;> decide

theorem escCharC_bytes (d : UData) (c : UInt32) (nxt : Option UInt32) :
    (escCharC d c nxt).flatMap writeChar = escChar d [ac 0x22] [] false false c nxt := by
  unfold escCharC
  split
  · rename_i h
    obtain ⟨h1, h2, h3⟩ := rawC_spec h
    rw [escChar_eq, h3, escP_raw _ _ c h1 h2]
    simp
  · exact flat_acB _

theorem escLoopC_bytes (d : UData) :
    ∀ cs, (escLoopC d cs).flatMap writeChar = escLoop d [ac 0x22] [] false false cs
  | [] => rfl
  | c :: rest => by
    rw [escLoopC, List.flatMap_append, escCharC_bytes, escLoopC_bytes d rest]
    rfl

/-! ## Each piece decodes to its char -/

/-- The next piece starts with a backslash or with the next char itself. -/
def LA (nxt : Option UInt32) (T : List UInt32) : Prop :=
  ∀ x, T.head? = some x → x = ac 0x5c ∨ nxt = some x

/-- The piece `P` of the char `c` starts with a backslash or with `c`, consists of
complete chars, is at most four times as long as `c`, and `unescape_string`
turns it back into the bytes of `c` in at most `P.length` steps when the next
piece follows. -/
def PieceOK (c : UInt32) (nxt : Option UInt32) (P : List UInt32) : Prop :=
  (P.head? = some (ac 0x5c) ∨ P.head? = some c) ∧ (∀ x ∈ P, Complete x) ∧
  (P.flatMap writeChar).length ≤ 4 * (writeChar c).length ∧
  ∀ T, LA nxt T → ∃ k, k ≤ P.length ∧
    ∀ f, unescLoop [] (f + k) (P ++ T) = (fun r => writeChar c ++ r) <$> unescLoop [] f T

theorem la_hex {nxt : Option UInt32} (hf : needFullHex nxt = false) {T : List UInt32}
    (hT : LA nxt T) : ∀ x, T.head? = some x → hexVal x = none := by
  intro x hx
  rcases hT x hx with rfl | rfl
  · decide
  · exact hexVal_none x hf

/-! ### ASCII chars -/

/-- An ASCII char's escape satisfies `unescSimple`'s preconditions. -/
def simpleB (e b : UInt8) : Bool :=
  !(acB e = ac 0x78 || acB e = ac 0x75 || acB e = ac 0x55) &&
  !(decide (ac 0x30 ≤ acB e) && decide (acB e ≤ ac 0x37)) &&
  unescSimple (acB e) == some (acB b)

/-- The four shapes of the escape of the ASCII byte `b`. -/
def kA (b : UInt8) (z : Bool) (P : List UInt8) : Bool :=
  asciiOut P && decide (P.length ≤ 4) &&
  ((P == [b] && b != 0x5c) ||
   (P == [0x5c, P.getD 1 0] && simpleB (P.getD 1 0) b) ||
   (P == hx b) ||
   (P == [0x5c, 0x30] && b == 0 && !z))

theorem kA_all : ∀ n : Fin 128, ∀ p z h : Bool,
    kA n.val.toUInt8 z (escCharP p z h (acB n.val.toUInt8)) = true := by
  decide +kernel

theorem ascii_tab : ∀ n : Fin 128, isasciiChar (acB n.val.toUInt8) = true := by decide +kernel

theorem kA_spec {b : UInt8} {z : Bool} {P : List UInt8} (h : kA b z P = true) :
    asciiOut P = true ∧ P.length ≤ 4 ∧
    ((P = [b] ∧ b ≠ 0x5c) ∨ (P = [0x5c, P.getD 1 0] ∧ simpleB (P.getD 1 0) b = true) ∨
     P = hx b ∨ (P = [0x5c, 0x30] ∧ b = 0 ∧ z = false)) := by
  unfold kA at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hA, hL⟩, hK⟩ := h
  refine ⟨hA, hL, ?_⟩
  rcases hK with ((h1 | h2) | h3) | h4
  · exact .inl h1
  · exact .inr (.inl h2)
  · exact .inr (.inr (.inl h3))
  · exact .inr (.inr (.inr ⟨h4.1.1, h4.1.2, h4.2⟩))


theorem pieceA (d : UData) (b : UInt8) (hb : b.toNat < 128) (nxt : Option UInt32) :
    PieceOK (acB b) nxt (escCharC d (acB b) nxt) := by
  have hasc : isasciiChar (acB b) = true := by
    have := ascii_tab ⟨b.toNat, hb⟩
    rwa [show (⟨b.toNat, hb⟩ : Fin 128).val.toUInt8 = b from u8_of b] at this
  have hraw : rawC d (acB b) = false := by unfold rawC; rw [hasc]; rfl
  have hk := kA_all ⟨b.toNat, hb⟩ (isprint d (acB b)) (octB nxt) (needFullHex nxt)
  rw [show (⟨b.toNat, hb⟩ : Fin 128).val.toUInt8 = b from u8_of b] at hk
  have hC : escCharC d (acB b) nxt =
      (escCharP (isprint d (acB b)) (octB nxt) (needFullHex nxt) (acB b)).map acB := by
    unfold escCharC; rw [if_neg (by rw [hraw]; decide), escChar_eq]
  rw [hC]
  obtain ⟨hA, hL, hK⟩ := kA_spec hk
  generalize escCharP (isprint d (acB b)) (octB nxt) (needFullHex nxt) (acB b) = P at hA hL hK ⊢
  have hwc : writeChar (acB b) = [b] := wc1 b
  refine ⟨?_, complete_ascii P hA, by rw [flat_acB, hwc]; simpa using hL, fun T hT => ?_⟩
  · rcases hK with ⟨rfl, _⟩ | ⟨h2, _⟩ | rfl | ⟨rfl, _, _⟩
    · exact .inr rfl
    · rw [h2]; exact .inl (by rw [← acB5c]; rfl)
    · rw [hx_map]; exact .inl rfl
    · exact .inl (by rw [← acB5c]; rfl)
  · rcases hK with ⟨rfl, hne⟩ | ⟨h2, hs⟩ | rfl | ⟨rfl, rfl, hz⟩
    · refine ⟨1, by simp, fun f => ?_⟩
      exact uloop_raw (acB b) T f (fun e => hne (acB_inj (e.trans acB5c.symm)))
    · generalize P.getD 1 0 = e at h2 hs
      subst h2
      simp only [simpleB, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hs
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      refine ⟨1, by simp, fun f => ?_⟩
      show unescLoop [] (f + 1) (acB 0x5c :: acB e :: T) = _
      rw [acB5c]
      exact U_simple (acB e) (acB b) T f h1 h2 h3
    · refine ⟨1, by rw [hx_map]; simp, fun f => ?_⟩
      rw [U_hx, hwc]
    · refine ⟨1, by simp, fun f => ?_⟩
      show unescLoop [] (f + 1) (acB 0x5c :: acB 0x30 :: T) = _
      rw [acB5c, show acB 0x30 = ac 0x30 by decide, hwc]
      exact U_oct0 T f (fun x hx => by
        rcases hT x hx with rfl | rfl
        · decide
        · exact hz)

/-! ### Malformed and overlong chars -/

theorem nonascii (c : UInt32) (h : 2147483648 ≤ c.toNat) : isasciiChar c = false := by
  unfold isasciiChar
  apply decide_eq_false
  rw [UInt32.lt_iff_toNat_lt, bswap_toNat]
  have : (0x80 : UInt32).toNat = 128 := rfl
  rw [this]; omega

theorem pieceX (d : UData) (c : UInt32) (hbig : 2147483648 ≤ c.toNat)
    (hwf : (!isoverlong c && !ismalformed c) = false) (nxt : Option UInt32) :
    PieceOK c nxt (escCharC d c nxt) := by
  have hasc := nonascii c hbig
  have hC : escCharC d c nxt = ((writeChar c).flatMap hx).map acB := by
    unfold escCharC
    rw [if_neg (by unfold rawC; rw [hasc, hwf]; simp), escChar_eq, escP_X _ _ _ c hasc hwf,
      hexBytes_eq]
    rfl
  rw [hC]
  obtain ⟨b0, bs, hw⟩ := wc_cons c
  refine ⟨?_, ?_, ?_, fun T _ => ⟨(writeChar c).length, ?_, fun f => U_hexbytes T (writeChar c) f⟩⟩
  · left; rw [hw, List.flatMap_cons, List.map_append, hx_map]; rfl
  · apply complete_ascii
    rw [show (writeChar c).flatMap hx = hexBytesAux 4 (bswap32 c) from (hexBytes_eq 4 _).symm]
    exact hexBytesAux_ascii 4 _
  · rw [flat_acB, flatMap_hx_len]; omega
  · rw [List.length_map, flatMap_hx_len]; omega

/-! ### Well-formed chars above ASCII -/

theorem enc2 (n : Nat) (h1 : 128 ≤ n) (h2 : n < 2048) :
    enc n = b4 (192 + n / 64) (128 + n % 64) 0 0 := by
  unfold JuliaLean.MissingChar.CharPf.enc; rw [if_neg (by omega), if_pos h2]

theorem enc3 (n : Nat) (h1 : 2048 ≤ n) (h2 : n < 65536) :
    enc n = b4 (224 + n / 4096) (128 + n / 64 % 64) (128 + n % 64) 0 := by
  unfold JuliaLean.MissingChar.CharPf.enc; rw [if_neg (by omega), if_neg (by omega), if_pos h2]

theorem enc4 (n : Nat) (h1 : 65536 ≤ n) :
    enc n = b4 (240 + n / 262144) (128 + n / 4096 % 64) (128 + n / 64 % 64) (128 + n % 64) := by
  unfold JuliaLean.MissingChar.CharPf.enc
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem enc_bounds (n : Nat) (h1 : 128 ≤ n) (h2 : n < 2097152) :
    3221225472 ≤ enc n ∧ (65536 ≤ n → 4026531840 ≤ enc n) ∧ (n < 65536 → enc n ≤ 4022320896) := by
  by_cases hb : n < 2048
  · rw [enc2 n h1 hb]; unfold JuliaLean.MissingChar.CharPf.b4
    exact ⟨by omega, fun _ => by omega, fun _ => by omega⟩
  by_cases hc : n < 65536
  · rw [enc3 n (by omega) hc]; unfold JuliaLean.MissingChar.CharPf.b4
    exact ⟨by omega, fun _ => by omega, fun _ => by omega⟩
  · rw [enc4 n (by omega)]; unfold JuliaLean.MissingChar.CharPf.b4
    exact ⟨by omega, fun _ => by omega, fun _ => by omega⟩

theorem complete_len (c : UInt32) (hc : Complete c) :
    ((writeChar c).length = 1 ∧ c.toNat < 2147483648) ∨
    ((writeChar c).length = 2 ∧ c.toNat < 3758096384) ∨
    ((writeChar c).length = 3 ∧ c.toNat < 4026531840) ∨ (writeChar c).length = 4 := by
  rcases hc with ⟨b0, h0, rfl⟩ | ⟨b0, b1, h0, h0', h1, h1', rfl⟩ |
    ⟨b0, b1, b2, h0, h0', h1, h1', h2, h2', rfl⟩ |
    ⟨b0, b1, b2, b3, h0, h0', h1, h1', h2, h2', h3, h3', rfl⟩
  · left; rw [wc1, v1]; exact ⟨rfl, by omega⟩
  · right; left; have := b1.toNat_lt; rw [wc2 _ _ h1, v2]; exact ⟨rfl, by omega⟩
  · right; right; left; have := b1.toNat_lt; have := b2.toNat_lt
    rw [wc3 _ _ _ h1 h2, v3]; exact ⟨rfl, by omega⟩
  · right; right; right; rw [wc4 _ _ _ _ h1 h2 h3]; rfl

theorem pieceHex (c : UInt32) (n : Nat) (e : UInt8) (m pad0 : Nat)
    (hm : (e = 0x75 ∧ m = 4 ∧ pad0 = 2) ∨ (e = 0x55 ∧ m = 8 ∧ pad0 = 4)) (nxt : Option UInt32)
    (hn : n ≤ 0x10ffff) (hnib : nibbles 16 n ≤ m) (hch : charOfCp n = c)
    (hlen : 2 + m ≤ 4 * (writeChar c).length) :
    PieceOK c nxt (([0x5c, e] ++ hexStr n (if false || needFullHex nxt then m else pad0)).map acB) := by
  have hm' : (e = 0x78 ∧ m = 2) ∨ (e = 0x75 ∧ m = 4) ∨ (e = 0x55 ∧ m = 8) := by
    rcases hm with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
    · exact .inr (.inl ⟨h1, h2⟩)
    · exact .inr (.inr ⟨h1, h2⟩)
  have hp0 : 2 ≤ pad0 ∧ pad0 < m := by rcases hm with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> omega
  obtain ⟨pad, hpad, hpm⟩ : ∃ pad, (if false || needFullHex nxt then m else pad0) = pad ∧
      (pad = m ∨ (pad = pad0 ∧ needFullHex nxt = false)) := by
    refine ⟨_, rfl, ?_⟩
    cases needFullHex nxt <;> simp
  rw [hpad]
  have hW1 : pad ≤ max pad (nibbles 16 n) := Nat.le_max_left _ _
  have hW2 : max pad (nibbles 16 n) ≤ m := Nat.max_le.mpr ⟨by omega, hnib⟩
  have hval : hfold 0 (hexDs n (max pad (nibbles 16 n))) = n :=
    hexStr_val n pad (by show n < 18446744073709551616; omega)
  have hA : asciiOut ([0x5c, e] ++ hexStr n pad) = true := by
    rw [asciiOut_append, hexStr_ascii, Bool.and_true]
    rcases hm with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> decide
  refine ⟨.inl ?_, complete_ascii _ hA, ?_, fun T hT => ⟨1, by simp, fun f => ?_⟩⟩
  · show some (acB 0x5c) = some (ac 0x5c); rw [acB5c]
  · rw [flat_acB, List.length_append, hexStr_len]
    show 2 + max pad (nibbles 16 n) ≤ _; omega
  · rw [piece_hex, U_hex e m hm' _ (hexDs_lt _ _) (by rw [hexDs_length]; omega)
      (by rw [hexDs_length]; omega) T ?_ (by rw [hval]; exact hn) f, hval]
    · unfold hexOut; rw [if_neg (by omega), hch]
    · intro hl
      rw [hexDs_length] at hl
      rcases hpm with rfl | ⟨rfl, hf⟩
      · omega
      · exact la_hex hf hT

theorem pieceM (d : UData) (c : UInt32) (hcomp : Complete c) (n : Nat) (hn1 : 128 ≤ n)
    (hn2 : n ≤ 0x10ffff) (hcn : c.toNat = enc n) (nxt : Option UInt32) :
    PieceOK c nxt (escCharC d c nxt) := by
  obtain ⟨hcp, hmal, hov⟩ := dec_all c n (by omega) hcn
  obtain ⟨hb1, hb2, hb3⟩ := enc_bounds n hn1 (by omega)
  have hbig : 2147483648 ≤ c.toNat := by rw [hcn]; omega
  have hasc := nonascii c hbig
  have hwf : (!isoverlong c && !ismalformed c) = true := by rw [hmal, hov]; rfl
  have hcpo : (cpOf c).toNat = n := by
    unfold cpOf; rw [hcp]
    show (UInt32.ofNat n).toNat = n
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by show n < 4294967296; omega)
  have hch : charOfCp n = c := by
    have ht : n.toUInt32.toNat = n := by
      show (UInt32.ofNat n).toNat = n
      rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by show n < 4294967296; omega)
    unfold charOfCp
    rw [charOfU32_ok _ (by rw [ht]; omega), ht]
    exact (eq_ofNat hcn).symm
  have hwl := complete_len c hcomp
  have hne5c : c ≠ ac 0x5c := fun e => by rw [e] at hbig; exact absurd hbig (by decide)
  by_cases hp : isprint d c = true
  · have hC : escCharC d c nxt = [c] := by
      unfold escCharC; rw [if_pos (by unfold rawC; rw [hasc, hwf, hp]; rfl)]
    rw [hC]
    refine ⟨.inr rfl, fun x hx => by simp at hx; subst hx; exact hcomp, ?_,
      fun T _ => ⟨1, by simp, fun f => uloop_raw c T f hne5c⟩⟩
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]; omega
  · have hp' : isprint d c = false := by simpa using hp
    have h7f : ¬ c ≤ ac 0x7f := by
      rw [UInt32.le_iff_toNat_le]
      have : (ac 0x7f).toNat = 2130706432 := by decide
      omega
    have hC0 : escCharC d c nxt = (escCharP false (octB nxt) (needFullHex nxt) c).map acB := by
      unfold escCharC; rw [if_neg (by unfold rawC; rw [hasc, hwf, hp']; decide), escChar_eq, hp']
    rw [hC0]
    have hle : (c ≤ 0xefbfbf00) ↔ c.toNat ≤ 4022320896 := by
      rw [UInt32.le_iff_toNat_le]; exact Iff.rfl
    by_cases hU : c ≤ 0xefbfbf00
    · have hn65 : n < 65536 := by
        rcases Nat.lt_or_ge n 65536 with h | h
        · exact h
        · have := hb2 h; have := hle.mp hU; omega
      rw [escP_u _ _ c hasc hwf h7f hU, hcpo, asc_u]
      exact pieceHex c n 0x75 4 2 (.inl ⟨rfl, rfl, rfl⟩) nxt hn2
        (nibbles_le 16 n 4 (by show n < 65536; omega)) hch (by omega)
    · have hn65 : 65536 ≤ n := by
        rcases Nat.lt_or_ge n 65536 with h | h
        · exact absurd (hle.mpr (by have := hb3 h; omega)) hU
        · exact h
      have := hb2 hn65
      rw [escP_U _ _ c hasc hwf h7f hU, hcpo, asc_U]
      exact pieceHex c n 0x55 8 4 (.inr ⟨rfl, rfl, rfl⟩) nxt hn2
        (nibbles_le 16 n 8 (by show n < 4294967296; omega)) hch (by omega)

/-! ## Classifying the chars of a string -/

/-- An ASCII char. -/
def IsA (c : UInt32) : Prop := ∃ b : UInt8, b.toNat < 128 ∧ c = acB b

/-- A non-ASCII char that is malformed or overlong: escaped byte by byte. -/
def IsX (c : UInt32) : Prop := 2147483648 ≤ c.toNat ∧ (!isoverlong c && !ismalformed c) = false

/-- A complete, well-formed, non-overlong char with code point in `0x80:0x10ffff`. -/
def IsM (c : UInt32) : Prop :=
  Complete c ∧ ∃ n, 128 ≤ n ∧ n ≤ 0x10ffff ∧ c.toNat = enc n

theorem mal_of (c : UInt32) (l t : Nat) (hl : clo32 c = l) (ht : land56 (ctz32 c) = t)
    (h : (ix (Int.ofNat l * 8) + ix t).val > 32) : ismalformed c = true := by
  unfold ismalformed
  dsimp only
  rw [hl, ht, decide_eq_true h]
  simp

theorem mal1_tab : ∀ n : Fin 256, 128 ≤ n.val → ismalformed (n.val.toUInt8.toUInt32 <<< 24) = true := by
  decide +kernel

theorem mal1 (b0 : UInt8) (h : 128 ≤ b0.toNat) : ismalformed (b0.toUInt32 <<< 24) = true := by
  have := mal1_tab ⟨b0.toNat, b0.toNat_lt⟩ h
  rwa [show (⟨b0.toNat, b0.toNat_lt⟩ : Fin 256).val.toUInt8 = b0 from u8_of b0] at this

theorem mal2 (b0 b1 : UInt8) (h0 : 224 ≤ b0.toNat) (h0' : b0.toNat ≤ 247) (h1 : 128 ≤ b1.toNat) :
    ismalformed (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) = true := by
  have hv := v2 b0 b1
  have := b1.toNat_lt
  have hct := ctz32_range (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) 16 (b0.toNat * 256 + b1.toNat)
    (by omega) (by rw [hv]; simp only [Nat.reducePow]; omega) (by omega)
  have ht : land56 (ctz32 (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16)) = 16 := by
    rw [land56_eq _ (by omega)]; omega
  by_cases hb : b0.toNat < 240
  · exact mal_of _ 3 16 (clo32_3 _ (by omega) (by omega)) ht (by decide)
  · exact mal_of _ 4 16 (clo32_4 _ (by omega) (by omega)) ht (by decide)

theorem mal3 (b0 b1 b2 : UInt8) (h0 : 240 ≤ b0.toNat) (h0' : b0.toNat ≤ 247) (h2 : 128 ≤ b2.toNat) :
    ismalformed (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) = true := by
  have hv := v3 b0 b1 b2
  have := b1.toNat_lt; have := b2.toNat_lt
  have hct := ctz32_range (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) 8
    (b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) (by omega)
    (by rw [hv]; simp only [Nat.reducePow]; omega) (by omega)
  have ht : land56 (ctz32 (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8)) = 8 := by
    rw [land56_eq _ (by omega)]; omega
  exact mal_of _ 4 8 (clo32_4 _ (by omega) (by omega)) ht (by decide)

theorem ov_true (c : UInt32)
    (h : c.toNat / 33554432 = 96 ∨ c.toNat / 2097152 = 1796 ∨ c.toNat / 1048576 = 3848) :
    isoverlong c = true := by
  rw [isoverlong_nat]; rcases h with h | h | h <;> simp [h]

theorem classify (c : UInt32) (hs : Shape c)
    (hH : ¬ (ismalformed c = false ∧ isoverlong c = false ∧ ∃ u, codepoint c = .ok u ∧ u > 0x10ffff)) :
    IsA c ∨ IsX c ∨ IsM c := by
  rcases hs with ⟨b0, rfl⟩ | ⟨b0, b1, h0, h0', h1, h1', rfl⟩ |
    ⟨b0, b1, b2, h0, h0', h1, h1', h2, h2', rfl⟩ |
    ⟨b0, b1, b2, b3, h0, h0', h1, h1', h2, h2', h3, h3', rfl⟩
  · by_cases hb : b0.toNat < 128
    · exact .inl ⟨b0, hb, rfl⟩
    · have := v1 b0
      refine .inr (.inl ⟨by omega, ?_⟩)
      rw [mal1 b0 (by omega)]; simp
  · have hv := v2 b0 b1
    have := b1.toNat_lt
    by_cases hm : 224 ≤ b0.toNat
    · refine .inr (.inl ⟨by omega, ?_⟩)
      rw [mal2 b0 b1 hm h0' h1]; simp
    by_cases ho : b0.toNat < 194
    · refine .inr (.inl ⟨by omega, ?_⟩)
      rw [ov_true _ (.inl (by omega))]; rfl
    refine .inr (.inr ⟨.inr (.inl ⟨b0, b1, h0, by omega, h1, h1', rfl⟩),
      (b0.toNat - 192) * 64 + (b1.toNat - 128), by omega, by omega, ?_⟩)
    rw [hv, enc2 _ (by omega) (by omega)]; unfold JuliaLean.MissingChar.CharPf.b4; omega
  · have hv := v3 b0 b1 b2
    have := b1.toNat_lt; have := b2.toNat_lt
    by_cases hm : 240 ≤ b0.toNat
    · refine .inr (.inl ⟨by omega, ?_⟩)
      rw [mal3 b0 b1 b2 hm h0' h2]; simp
    by_cases ho : b0.toNat = 224 ∧ b1.toNat < 160
    · refine .inr (.inl ⟨by omega, ?_⟩)
      rw [ov_true _ (.inr (.inl (by omega)))]; rfl
    refine .inr (.inr ⟨.inr (.inr (.inl ⟨b0, b1, b2, h0, by omega, h1, h1', h2, h2', rfl⟩)),
      (b0.toNat - 224) * 4096 + (b1.toNat - 128) * 64 + (b2.toNat - 128), by omega, by omega, ?_⟩)
    rw [hv, enc3 _ (by omega) (by omega)]; unfold JuliaLean.MissingChar.CharPf.b4; omega
  · have hv := v4 b0 b1 b2 b3
    have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    by_cases ho : b0.toNat = 240 ∧ b1.toNat < 144
    · refine .inr (.inl ⟨by omega, ?_⟩)
      rw [ov_true _ (.inr (.inr (by omega)))]; rfl
    have hcn : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32).toNat =
        enc ((b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 +
          (b3.toNat - 128)) := by
      rw [hv, enc4 _ (by omega)]; unfold JuliaLean.MissingChar.CharPf.b4; omega
    by_cases hbig : (b0.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 + (b2.toNat - 128) * 64 +
        (b3.toNat - 128) ≤ 0x10ffff
    · exact .inr (.inr ⟨.inr (.inr (.inr ⟨b0, b1, b2, b3, h0, h0', h1, h1', h2, h2', h3, h3', rfl⟩)),
        _, by omega, hbig, hcn⟩)
    · exfalso
      obtain ⟨hcp, hmal, hov⟩ := dec_all _ _ (by omega) hcn
      refine hH ⟨hmal, hov, _, hcp, ?_⟩
      show (1114111 : UInt32) < _
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by show _ < 4294967296; omega)]
      show 1114111 < _; omega

/-! ## The whole string -/

theorem piece_ok (d : UData) (c : UInt32) (nxt : Option UInt32) (h : IsA c ∨ IsX c ∨ IsM c) :
    PieceOK c nxt (escCharC d c nxt) := by
  rcases h with ⟨b, hb, rfl⟩ | ⟨hbig, hwf⟩ | ⟨hcomp, n, hn1, hn2, hcn⟩
  · exact pieceA d b hb nxt
  · exact pieceX d c hbig hwf nxt
  · exact pieceM d c hcomp n hn1 hn2 hcn nxt

theorem mk_bytes (b : List UInt8) (h : b.length < 2 ^ 62) : (JStr.mk b h).bytes = b := rfl

theorem esc_ok (d : UData) (s : JStr)
    (hR : (escLoop d [ac 0x22] [] false false (chars s)).length < 2 ^ 62) :
    escapeString d s = .ok ⟨_, hR⟩ := by
  unfold escapeString escapeStringIO mkStr
  rw [dif_pos hR]

theorem head_app {P T : List UInt32} {y : UInt32} (h : P.head? = some y) : (P ++ T).head? = some y := by
  cases P with
  | nil => simp at h
  | cons a P => simpa using h

theorem main_unesc (d : UData) : ∀ cs : List UInt32, (∀ c ∈ cs, IsA c ∨ IsX c ∨ IsM c) →
    (∀ x ∈ escLoopC d cs, Complete x) ∧
    ((escLoopC d cs).flatMap writeChar).length ≤ 4 * (cs.flatMap writeChar).length ∧
    LA cs.head? (escLoopC d cs) ∧
    ∀ f, (escLoopC d cs).length < f → unescLoop [] f (escLoopC d cs) = .ok (cs.flatMap writeChar)
  | [], _ => ⟨fun x hx => by simp [escLoopC] at hx, by simp [escLoopC],
      fun x hx => by simp [escLoopC] at hx, fun f _ => uloop_nil f⟩
  | c :: rest, hcs => by
    obtain ⟨ih1, ih2, ih3, ih4⟩ := main_unesc d rest (fun x hx => hcs x (by simp [hx]))
    obtain ⟨hh, hc, hb, hu⟩ := piece_ok d c rest.head? (hcs c (by simp))
    obtain ⟨k, hk, hk'⟩ := hu (escLoopC d rest) ih3
    show (∀ x ∈ escCharC d c rest.head? ++ escLoopC d rest, Complete x) ∧
      ((escCharC d c rest.head? ++ escLoopC d rest).flatMap writeChar).length ≤
        4 * ((c :: rest).flatMap writeChar).length ∧
      LA (some c) (escCharC d c rest.head? ++ escLoopC d rest) ∧
      ∀ f, (escCharC d c rest.head? ++ escLoopC d rest).length < f →
        unescLoop [] f (escCharC d c rest.head? ++ escLoopC d rest) = .ok ((c :: rest).flatMap writeChar)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hc x h
      · exact ih1 x h
    · rw [List.flatMap_append, List.length_append, List.flatMap_cons, List.length_append]; omega
    · intro x hx
      rcases hh with h | h
      · rw [head_app h] at hx; exact .inl (Option.some.inj hx).symm
      · rw [head_app h] at hx; exact .inr (by rw [Option.some.inj hx])
    · intro f hf
      rw [List.length_append] at hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + k := ⟨f - k, by omega⟩
      rw [hk' f', ih4 f' (by omega)]
      rfl

theorem len_ok (d : UData) (s : JStr) (hlen : s.bytes.length < 2 ^ 59)
    (hsize : ((escLoopC d (chars s)).flatMap writeChar).length ≤ 4 * s.bytes.length) :
    (escLoop d [ac 0x22] [] false false (chars s)).length < 2 ^ 62 := by
  rw [← escLoopC_bytes d (chars s)]
  have e59 : (2 : Nat) ^ 59 = 576460752303423488 := rfl
  have e62 : (2 : Nat) ^ 62 = 4611686018427387904 := rfl
  rw [e62]; rw [e59] at hlen; omega

theorem uso_ok (cs : List UInt32) (s : JStr) (h : unescLoop [] (cs.length + 1) cs = .ok s.bytes) :
    unescapeStringOf cs [] = .ok s := by
  unfold unescapeStringOf
  rw [h]
  show mkStr s.bytes = _
  unfold mkStr; rw [dif_pos s.small]

theorem us_eq (R : JStr) : unescapeString R = unescapeStringOf (chars R) [] := rfl

theorem unesc_ok (d : UData) (s : JStr)
    (hR : (escLoop d [ac 0x22] [] false false (chars s)).length < 2 ^ 62)
    (hcomp : ∀ x ∈ escLoopC d (chars s), Complete x)
    (hun : ∀ f, (escLoopC d (chars s)).length < f →
      unescLoop [] f (escLoopC d (chars s)) = .ok ((chars s).flatMap writeChar)) :
    unescapeString ⟨_, hR⟩ = .ok s := by
  have hch : chars ⟨_, hR⟩ = escLoopC d (chars s) :=
    chars_of_complete ⟨_, hR⟩ (escLoopC d (chars s))
      ((mk_bytes _ hR).trans (escLoopC_bytes d (chars s)).symm) hcomp
  rw [us_eq]
  apply uso_ok
  rw [hch, hun _ (by omega), (chars_spec s).1]

end EscRT

open EscRT in
theorem escapeRoundTripInRange_proven : EscapeRoundTripInRange := by
  intro d s hlen hH
  have hcls : ∀ c ∈ chars s, IsA c ∨ IsX c ∨ IsM c :=
    fun c hc => classify c (chars_shape s c hc) (hH c hc)
  obtain ⟨hcomp, hsize, -, hun⟩ := main_unesc d (chars s) hcls
  rw [(chars_spec s).1] at hsize
  have hR := len_ok d s hlen hsize
  exact ⟨⟨_, hR⟩, s, esc_ok d s hR, unesc_ok d s hR hcomp hun, rfl⟩

end JuliaLean.Show
