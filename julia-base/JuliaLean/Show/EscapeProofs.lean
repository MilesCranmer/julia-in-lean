import JuliaLean.Show.Escape
import JuliaLean.Strings.Theory

/-!
# Properties of `escape_string`, `unescape_string` and `repr(::Char)`
-/

namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-! ## Statements -/

/-- `unescape_string(escape_string(s)) == s` (`escape_string` docstring,
`base/strings/io.jl:399-454`: "See also `unescape_string` for the reverse
operation"), with the default arguments. -/
def EscapeRoundTrip : Prop :=
  ∀ (d : UData) (s : JStr), ∃ r t, escapeString d s = .ok r ∧ unescapeString r = .ok t ∧ t.bytes = s.bytes

/-- `repr(c)` for every char `c` of a string is a character literal that the
parser reads back as `c`: the body between the quotes decodes, by
`unescape_julia_string`, to exactly the bytes of `c`
(`JuliaSyntax/src/julia/literal_parsing.jl:386-397`). -/
def CharReprParses : Prop :=
  ∀ (d : UData) (s : JStr) (c : UInt32), c ∈ chars s →
    ∃ body, showChar d c = [0x27] ++ body ++ [0x27] ∧ juliaUnescape body = some (charBytes c)

/-- `escape_string(s; ascii = true, fullhex)` only produces ASCII bytes
(docstring: "`ascii` can be set to `true` to escape all non-ASCII characters"). -/
def EscapeAsciiOutput : Prop :=
  ∀ (d : UData) (s : JStr) (fullhex : Bool) (r : JStr),
    escapeString d s (ascii := true) (fullhex := fullhex) = .ok r → ∀ b ∈ r.bytes, b < 0x80

/-! ## Helper lemmas -/

/-- Every byte is ASCII. -/
def asciiOut (l : List UInt8) : Bool := l.all (fun b => decide (b < 0x80))

theorem asciiOut_append (a b : List UInt8) : asciiOut (a ++ b) = (asciiOut a && asciiOut b) := by
  simp [asciiOut, List.all_append]

theorem asciiOut_cons (x : UInt8) (b : List UInt8) :
    asciiOut (x :: b) = (decide (x < 0x80) && asciiOut b) := by
  simp [asciiOut]

theorem hexDigit_lt : ∀ d < 16, hexDigit d < 0x80 := by decide

theorem hexStr_ascii (x p : Nat) : asciiOut (hexStr x p) = true := by
  simp only [asciiOut, hexStr, List.all_map, List.all_eq_true, Function.comp, decide_eq_true_eq]
  intro i _
  exact hexDigit_lt _ (Nat.mod_lt _ (by decide))

theorem hexBytesAux_ascii : ∀ (k : Nat) (u : UInt32), asciiOut (hexBytesAux k u) = true
  | 0, _ => rfl
  | k + 1, u => by
    simp only [hexBytesAux, asciiOut_append, hexStr_ascii]
    split
    · rfl
    · simp only [hexBytesAux_ascii k]; rfl

theorem escapeNul_ascii (n : Option UInt32) : asciiOut (escapeNul n) = true := by
  cases n with
  | none => rfl
  | some c => simp only [escapeNul]; split <;> rfl

theorem getD_mem_or {α : Type} : ∀ (l : List α) (i : Nat) (x : α), l.getD i x ∈ l ∨ l.getD i x = x
  | [], _, _ => .inr rfl
  | a :: l, 0, _ => .inl (by simp)
  | a :: l, i + 1, x => by
    rcases getD_mem_or l i x with h | h
    · exact .inl (by simp at h ⊢; exact .inr h)
    · exact .inr (by simpa using h)

theorem uint32_eq_zero_of_toNat (u : UInt32) (h : u.toNat = 0) : u = 0 := by
  have : u.toNat = (0 : UInt32).toNat := h
  exact UInt32.toNat_inj.mp this

theorem writeChar_ascii (c : UInt32) (h : isasciiChar c = true) : asciiOut (writeChar c) = true := by
  have hu : (bswap32 c).toNat < 128 := by
    have : bswap32 c < 0x80 := by simpa [isasciiChar] using h
    exact UInt32.lt_iff_toNat_lt.mp this
  have hs : bswap32 c >>> 8 = 0 := by
    apply uint32_eq_zero_of_toNat
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have : (8 : UInt32).toNat % 32 = 8 := rfl
    rw [this]; omega
  unfold writeChar writeCharAux
  rw [if_pos hs, asciiOut_cons]
  have : (bswap32 c).toUInt8 < 0x80 := by
    rw [UInt8.lt_iff_toNat_lt, UInt32.toNat_toUInt8]; simp; omega
  simp [this]; rfl

theorem escChar_ascii (d : UData) (fh : Bool) (c : UInt32) (nxt : Option UInt32) :
    asciiOut (escChar d [ac 0x22] [] true fh c nxt) = true := by
  unfold escChar
  split
  · rename_i h; simp at h; subst h; decide
  split
  · rename_i h; simp at h
  split
  · rename_i ha
    split
    · exact escapeNul_ascii nxt
    split
    · rfl
    split
    · rfl
    split
    · have hx : (asc ['a', 'b', 't', 'n', 'v', 'f', 'r']).getD ((cpOf c).toNat - 7) 0 < 0x80 := by
        rcases getD_mem_or (asc ['a', 'b', 't', 'n', 'v', 'f', 'r']) ((cpOf c).toNat - 7) 0 with h | h
        · have : ∀ x ∈ asc ['a', 'b', 't', 'n', 'v', 'f', 'r'], x < 0x80 := by decide
          exact this _ h
        · rw [h]; decide
      rw [asciiOut_cons, asciiOut_cons, decide_eq_true hx]; rfl
    split
    · exact writeChar_ascii c ha
    · rw [asciiOut_append, hexStr_ascii]; rfl
  split
  · split
    · rename_i h; simp at h
    split
    · rw [asciiOut_append, hexStr_ascii]; rfl
    split
    · rw [asciiOut_append, hexStr_ascii]; rfl
    · rw [asciiOut_append, hexStr_ascii]; rfl
  · exact hexBytesAux_ascii 4 _

theorem escLoop_ascii (d : UData) (fh : Bool) :
    ∀ cs, asciiOut (escLoop d [ac 0x22] [] true fh cs) = true
  | [] => rfl
  | c :: cs => by
    simp only [escLoop, asciiOut_append, escChar_ascii, escLoop_ascii d fh cs]; rfl

theorem mkStr_bytes {bs : List UInt8} {r : JStr} (h : mkStr bs = .ok r) : r.bytes = bs := by
  unfold mkStr at h
  by_cases hl : bs.length < 2 ^ 62
  · rw [dif_pos hl] at h; cases h; rfl
  · rw [dif_neg hl] at h; cases h

theorem jstr_ext {a b : JStr} (h : a.bytes = b.bytes) : a = b := by
  cases a; cases b; simp_all

/-! ## Results -/

theorem escapeAsciiOutput_proven : EscapeAsciiOutput := by
  intro d s fh r h b hb
  have hr := mkStr_bytes h
  rw [hr] at hb
  have := escLoop_ascii d fh (chars s)
  simp only [asciiOut, List.all_eq_true, decide_eq_true_eq] at this
  exact this b hb

/-- The four bytes `f4 90 80 80`: one well-formed char with code point `0x110000`. -/
def strAbove : JStr := ⟨[0xf4, 0x90, 0x80, 0x80], by decide⟩

/-- The bytes `\U110000`, as `escape_string` prints `strAbove`. -/
def strAboveEsc : JStr := ⟨asc ['\\', 'U', '1', '1', '0', '0', '0', '0'], by decide⟩

theorem escapeRoundTrip_refuted : ¬ EscapeRoundTrip := by
  intro h
  obtain ⟨r, t, h1, h2, _⟩ := h UData.empty strAbove
  have e1 : (escapeString UData.empty strAbove).toOption.map JStr.bytes = some strAboveEsc.bytes := by
    decide
  rw [h1] at e1
  have hr : r = strAboveEsc := jstr_ext (by simpa [Except.toOption] using e1)
  subst hr
  have e2 : (unescapeString strAboveEsc).isOk = false := by decide
  rw [h2] at e2
  cases e2

theorem charReprParses_refuted : ¬ CharReprParses := by
  intro h
  obtain ⟨body, h1, h2⟩ := h UData.empty strAbove 0xf4908080 (by decide)
  have e1 : showChar UData.empty 0xf4908080 = [0x27] ++ strAboveEsc.bytes ++ [0x27] := by decide
  rw [e1] at h1
  have hb : body = strAboveEsc.bytes := (by simpa using h1 : strAboveEsc.bytes = body).symm
  subst hb
  revert h2
  decide

/-! ## `write(io, c)` as arithmetic -/

/-- `writeCharAux` on the natural number value of `u`. -/
def wNat : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => n.toUInt8 :: (if n / 256 = 0 then [] else wNat k (n / 256))

theorem u32_toUInt8 (u : UInt32) : u.toUInt8 = u.toNat.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp [UInt32.toNat_toUInt8]

theorem shr8_toNat (u : UInt32) : (u >>> 8).toNat = u.toNat / 256 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl

theorem writeCharAux_eq : ∀ (k : Nat) (u : UInt32), writeCharAux k u = wNat k u.toNat
  | 0, _ => rfl
  | k + 1, u => by
    have hz : (u >>> 8 = 0) ↔ u.toNat / 256 = 0 := by
      rw [← shr8_toNat]
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact UInt32.toNat_inj.mp (by rw [h]; rfl)
    simp only [writeCharAux, wNat, u32_toUInt8, writeCharAux_eq k (u >>> 8), shr8_toNat]
    by_cases h : u.toNat / 256 = 0
    · rw [if_pos (hz.mpr h), if_pos h]
    · rw [if_neg (mt hz.mp h), if_neg h]

/-- Little-endian value of a byte list. -/
def leVal : List UInt8 → Nat
  | [] => 0
  | b :: l => b.toNat + 256 * leVal l

theorem leVal_ne_zero (y : UInt8) (l : List UInt8) (h : y ≠ 0) : leVal (y :: l) ≠ 0 := by
  have : y.toNat ≠ 0 := fun e => h (UInt8.toNat_inj.mp (by rw [e]; rfl))
  simp only [leVal]; omega

theorem wNat_bytes : ∀ (rest : List UInt8) (b : UInt8) (k : Nat), rest.length < k →
    (∀ x ∈ rest, x ≠ 0) → wNat k (leVal (b :: rest)) = b :: rest
  | [], b, k + 1, _, _ => by
    have := b.toNat_lt
    have e1 : leVal [b] / 256 = 0 := by simp only [leVal]; omega
    rw [wNat, if_pos e1]
    congr 1
    apply UInt8.toNat_inj.mp; simp [leVal]
  | y :: rest, b, k + 1, hk, hnz => by
    have := b.toNat_lt
    simp only [wNat]
    have hv : leVal (y :: rest) ≠ 0 := leVal_ne_zero y rest (hnz y (by simp))
    have e1 : leVal (b :: y :: rest) / 256 = leVal (y :: rest) := by
      simp only [leVal] at hv ⊢; omega
    rw [e1, if_neg hv, wNat_bytes rest y k (by simp at hk; omega) (fun x hx => hnz x (by simp [hx]))]
    congr 1
    apply UInt8.toNat_inj.mp; simp [leVal] <;> omega

theorem or_toNat_disjoint (x y : UInt32) (k : Nat) (hx : x.toNat % 2 ^ k = 0) (hy : y.toNat < 2 ^ k) :
    (x ||| y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_or]
  have e : x.toNat = (x.toNat / 2 ^ k) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hx)]
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt hy]

theorem bswap_toNat (x : UInt32) : (bswap32 x).toNat = x.toNat % 256 * 16777216 +
    x.toNat / 256 % 256 * 65536 + x.toNat / 65536 % 256 * 256 + x.toNat / 16777216 := by
  have hx := x.toNat_lt
  have ff : (0xff : UInt32).toNat = 2 ^ 8 - 1 := rfl
  have a1 : ((x &&& 0xff) <<< 24).toNat = x.toNat % 256 * 16777216 := by
    rw [UInt32.toNat_shiftLeft, UInt32.toNat_and, ff, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
    have : (24 : UInt32).toNat % 32 = 24 := rfl
    rw [this]; simp only [Nat.reducePow] at *; omega
  have a2 : (((x >>> 8) &&& 0xff) <<< 16).toNat = x.toNat / 256 % 256 * 65536 := by
    rw [UInt32.toNat_shiftLeft, UInt32.toNat_and, ff, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq,
      shr8_toNat]
    have : (16 : UInt32).toNat % 32 = 16 := rfl
    rw [this]; simp only [Nat.reducePow] at *; omega
  have a3 : (((x >>> 16) &&& 0xff) <<< 8).toNat = x.toNat / 65536 % 256 * 256 := by
    rw [UInt32.toNat_shiftLeft, UInt32.toNat_and, ff, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq,
      UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have : (8 : UInt32).toNat % 32 = 8 := rfl
    have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
    rw [this, h16]; simp only [Nat.reducePow] at *; omega
  have a4 : (x >>> 24).toNat = x.toNat / 16777216 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  unfold bswap32
  have hAB := or_toNat_disjoint ((x &&& 0xff) <<< 24) (((x >>> 8) &&& 0xff) <<< 16) 24
    (by rw [a1]; simp only [Nat.reducePow]; omega) (by rw [a2]; simp only [Nat.reducePow]; omega)
  have hABC := or_toNat_disjoint (((x &&& 0xff) <<< 24) ||| (((x >>> 8) &&& 0xff) <<< 16))
    (((x >>> 16) &&& 0xff) <<< 8) 16
    (by rw [hAB, a1, a2]; simp only [Nat.reducePow]; omega) (by rw [a3]; simp only [Nat.reducePow]; omega)
  rw [or_toNat_disjoint _ _ 8 (by rw [hABC, hAB, a1, a2, a3]; simp only [Nat.reducePow]; omega)
    (by rw [a4]; simp only [Nat.reducePow]; omega), hABC, hAB, a1, a2, a3, a4]

theorem writeChar_of_val (c : UInt32) (b : UInt8) (rest : List UInt8) (hk : rest.length ≤ 3)
    (hnz : ∀ x ∈ rest, x ≠ 0) (hv : (bswap32 c).toNat = leVal (b :: rest)) :
    writeChar c = b :: rest := by
  unfold writeChar
  rw [writeCharAux_eq, hv]
  exact wNat_bytes rest b 4 (by omega) hnz

/-! ## The chars of an iteration -/

theorem v1 (b0 : UInt8) : (b0.toUInt32 <<< 24).toNat = b0.toNat * 16777216 := by
  rw [shl24_toNat]

theorem v2 (b0 b1 : UInt8) : ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16)).toNat =
    b0.toNat * 16777216 + b1.toNat * 65536 := by
  have := b1.toNat_lt
  rw [or_toNat_disjoint _ _ 24 (by rw [v1]; omega) (by rw [shl16_toNat]; simp only [Nat.reducePow] at *; omega),
    v1, shl16_toNat]

theorem v3 (b0 b1 b2 : UInt8) :
    ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8)).toNat =
    b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 := by
  have := b2.toNat_lt
  rw [or_toNat_disjoint _ _ 16 (by rw [v2]; omega) (by rw [shl8_toNat]; simp only [Nat.reducePow] at *; omega),
    v2, shl8_toNat]

theorem v4 (b0 b1 b2 b3 : UInt8) :
    ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32).toNat =
    b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat := by
  have := b3.toNat_lt
  rw [or_toNat_disjoint _ _ 8 (by rw [v3]; omega) (by rw [UInt8.toNat_toUInt32]; simp only [Nat.reducePow] at *; omega),
    v3, UInt8.toNat_toUInt32]

theorem u8_ne_zero {b : UInt8} (h : 128 ≤ b.toNat) : b ≠ 0 := by
  intro e; rw [e] at h; simp at h

theorem wc1 (b0 : UInt8) : writeChar (b0.toUInt32 <<< 24) = [b0] := by
  have := b0.toNat_lt
  apply writeChar_of_val _ _ _ (by simp) (by simp)
  rw [bswap_toNat, v1]; simp only [leVal, Nat.reducePow] at *; omega

theorem wc2 (b0 b1 : UInt8) (h1 : 128 ≤ b1.toNat) :
    writeChar ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16)) = [b0, b1] := by
  have := b0.toNat_lt; have := b1.toNat_lt
  apply writeChar_of_val _ _ _ (by simp) (by simp [u8_ne_zero h1])
  rw [bswap_toNat, v2]; simp only [leVal, Nat.reducePow] at *; omega

theorem wc3 (b0 b1 b2 : UInt8) (h1 : 128 ≤ b1.toNat) (h2 : 128 ≤ b2.toNat) :
    writeChar ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8)) = [b0, b1, b2] := by
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt
  apply writeChar_of_val _ _ _ (by simp) (by simp [u8_ne_zero h1, u8_ne_zero h2])
  rw [bswap_toNat, v3]; simp only [leVal, Nat.reducePow] at *; omega

theorem u8lt256 (b : UInt8) : b.toNat < 256 := b.toNat_lt

theorem mod5 (a b c : Nat) (hc : c < 256) : (a * 65536 + b * 256 + c) % 256 = c := by omega

theorem mod6 (a b : Nat) (hb : b < 256) : (a * 256 + b) % 256 = b := by omega

theorem bswap4_arith (a b c e : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (he : e < 256) :
    (a * 16777216 + b * 65536 + c * 256 + e) % 256 * 16777216 +
      (a * 16777216 + b * 65536 + c * 256 + e) / 256 % 256 * 65536 +
      (a * 16777216 + b * 65536 + c * 256 + e) / 65536 % 256 * 256 +
      (a * 16777216 + b * 65536 + c * 256 + e) / 16777216 =
    a + 256 * (b + 256 * (c + 256 * (e + 256 * 0))) := by
  have d1 : (a * 16777216 + b * 65536 + c * 256 + e) % 256 = e := by omega
  have d2 : (a * 16777216 + b * 65536 + c * 256 + e) / 256 = a * 65536 + b * 256 + c := by omega
  have d3 : (a * 16777216 + b * 65536 + c * 256 + e) / 65536 = a * 256 + b := by omega
  have d4 : (a * 16777216 + b * 65536 + c * 256 + e) / 16777216 = a := by omega
  have d5 : (a * 65536 + b * 256 + c) % 256 = c := mod5 a b c hc
  have d6 : (a * 256 + b) % 256 = b := mod6 a b hb
  rw [d1, d2, d3, d4, d5, d6]
  omega

theorem wc4 (b0 b1 b2 b3 : UInt8) (h1 : 128 ≤ b1.toNat) (h2 : 128 ≤ b2.toNat) (h3 : 128 ≤ b3.toNat) :
    writeChar ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32) =
      [b0, b1, b2, b3] := by
  apply writeChar_of_val _ _ _ (by simp) (by simp [u8_ne_zero h1, u8_ne_zero h2, u8_ne_zero h3])
  rw [bswap_toNat, v4]
  exact bswap4_arith _ _ _ _ (u8lt256 b0) (u8lt256 b1) (u8lt256 b2) (u8lt256 b3)

/-- The chars `iterate` produces: a single byte, or bytes that are all `≥ 0x80`. -/
def GoodChar (c : UInt32) : Prop :=
  (∃ b : UInt8, c = b.toUInt32 <<< 24 ∧ writeChar c = [b]) ∨
    (writeChar c ≠ [] ∧ ∀ x ∈ writeChar c, 0x80 ≤ x)

theorem dt (L : List UInt8) (q m : Nat) (h : q < L.length) :
    (L.drop q).take (m + 1) = L.getD q 0 :: (L.drop (q + 1)).take m := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem cu_eq (s : JStr) (i : JInt64) : cu s i = s.bytes.getD (i.val.toNat - 1) 0 := rfl

theorem le80 {b : UInt8} (h : 128 ≤ b.toNat) : (0x80 : UInt8) ≤ b := by
  rw [UInt8.le_iff_toNat_le]; exact h

/-- What one `iterate` step from `p` produced: `c`, with next index `j = p + m`,
writes the `m` bytes at `p`. -/
def StepOK (s : JStr) (p : JInt64) (c : UInt32) (j : JInt64) : Prop :=
  ∃ m : Nat, j.val = p.val + m ∧ 1 ≤ m ∧ p.val + m ≤ s.bytes.length + 1 ∧
    writeChar c = (s.bytes.drop (p.val.toNat - 1)).take m ∧ GoodChar c

theorem iterate_step (s : JStr) (p : JInt64) (h1 : 1 ≤ p.val) (h2 : p.val ≤ s.bytes.length) :
    ∃ c j, iterate s p = some (c, j) ∧ StepOK s p c j := by
  have hs := ncu_small s
  have e1 : (p + ix 1).val = p.val + 1 := add1_val _ (by omega) (by omega)
  have e2 : (p + ix 1 + ix 1).val = p.val + 2 := by rw [add1_val _ (by omega) (by omega), e1]; omega
  have e3 : (p + ix 1 + ix 1 + ix 1).val = p.val + 3 := by rw [add1_val _ (by omega) (by omega), e2]; omega
  have e4 : (p + ix 1 + ix 1 + ix 1 + ix 1).val = p.val + 4 := by
    rw [add1_val _ (by omega) (by omega), e3]; omega
  have b0l := (cu s p).toNat_lt
  have hB1 : cu s (p + ix 1) = s.bytes.getD (p.val.toNat - 1 + 1) 0 := by rw [cu_eq, e1]; congr 1; omega
  have hB2 : cu s (p + ix 1 + ix 1) = s.bytes.getD (p.val.toNat - 1 + 2) 0 := by
    rw [cu_eq, e2]; congr 1; omega
  have hB3 : cu s (p + ix 1 + ix 1 + ix 1) = s.bytes.getD (p.val.toNat - 1 + 3) 0 := by
    rw [cu_eq, e3]; congr 1; omega
  have one : ∀ j : JInt64, j.val = p.val + 1 → StepOK s p ((cu s p).toUInt32 <<< 24) j := by
    intro j hj
    refine ⟨1, hj, Nat.le_refl _, by omega, ?_, .inl ⟨cu s p, rfl, wc1 _⟩⟩
    rw [wc1, dt _ _ _ (by omega), cu_eq]; simp
  have two : ∀ j : JInt64, j.val = p.val + 2 → 192 ≤ (cu s p).toNat → 128 ≤ (cu s (p + ix 1)).toNat →
      p.val + 1 ≤ s.bytes.length →
      StepOK s p ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16) j := by
    intro j hj hb0 hc1 hl
    have hw := wc2 (cu s p) (cu s (p + ix 1)) hc1
    refine ⟨2, hj, by omega, by omega, ?_, .inr ⟨by rw [hw]; simp, ?_⟩⟩
    · rw [hw, dt _ _ _ (by omega), dt _ _ _ (by omega), cu_eq, hB1]; simp
    · rw [hw]; intro x hx; simp at hx
      rcases hx with rfl | rfl
      · exact le80 (by omega)
      · exact le80 hc1
  have three : ∀ j : JInt64, j.val = p.val + 3 → 192 ≤ (cu s p).toNat → 128 ≤ (cu s (p + ix 1)).toNat →
      128 ≤ (cu s (p + ix 1 + ix 1)).toNat → p.val + 2 ≤ s.bytes.length →
      StepOK s p ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16 |||
        (cu s (p + ix 1 + ix 1)).toUInt32 <<< 8) j := by
    intro j hj hb0 hc1 hc2 hl
    have hw := wc3 (cu s p) (cu s (p + ix 1)) (cu s (p + ix 1 + ix 1)) hc1 hc2
    refine ⟨3, hj, by omega, by omega, ?_, .inr ⟨by rw [hw]; simp, ?_⟩⟩
    · rw [hw, dt _ _ _ (by omega), dt _ _ _ (by omega), dt _ _ _ (by omega), cu_eq, hB1, hB2]; simp
    · rw [hw]; intro x hx; simp at hx
      rcases hx with rfl | rfl | rfl
      · exact le80 (by omega)
      · exact le80 hc1
      · exact le80 hc2
  have c0 : ((cu s p).toUInt32 <<< 24 < 0xc0000000) ↔ (cu s p).toNat < 192 := by
    rw [UInt32.lt_iff_toNat_lt, v1]
    have : (0xc0000000 : UInt32).toNat = 3221225472 := rfl
    rw [this]; omega
  have c1 : ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16 < 0xe0000000) ↔
      (cu s p).toNat < 224 := by
    have := (cu s (p + ix 1)).toNat_lt
    rw [UInt32.lt_iff_toNat_lt, v2]
    have : (0xe0000000 : UInt32).toNat = 3758096384 := rfl
    rw [this]; omega
  have c2 : ((cu s p).toUInt32 <<< 24 ||| (cu s (p + ix 1)).toUInt32 <<< 16 |||
      (cu s (p + ix 1 + ix 1)).toUInt32 <<< 8 < 0xf0000000) ↔ (cu s p).toNat < 240 := by
    have := (cu s (p + ix 1)).toNat_lt; have := (cu s (p + ix 1 + ix 1)).toNat_lt
    rw [UInt32.lt_iff_toNat_lt, v3]
    have : (0xf0000000 : UInt32).toNat = 4026531840 := rfl
    rw [this]; omega
  rw [iterate_eq s p h1 h2]
  by_cases hb : (!between (cu s p) 0x80 0xf7) = true
  · rw [if_pos hb]; exact ⟨_, _, rfl, one _ e1⟩
  rw [if_neg hb]
  rcases hr : iterateContinued s p ((cu s p).toUInt32 <<< 24) with ⟨u, j⟩
  refine ⟨u, j, rfl, ?_⟩
  unfold iterateContinued at hr
  dsimp only at hr
  split at hr
  next h0 =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr; exact one _ e1
  next h0 =>
  have hb0 : 192 ≤ (cu s p).toNat := by have := mt c0.mpr h0; omega
  split at hr
  next hl =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr; exact one _ e1
  next hl =>
  rw [e1, ncu_val] at hl
  split at hr
  next hc =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr; exact one _ e1
  next hc =>
  have hc1 : 128 ≤ (cu s (p + ix 1)).toNat ∧ (cu s (p + ix 1)).toNat < 192 := by
    rw [isCont_eq] at hc; simpa using hc
  split at hr
  next hl2 =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    exact two _ e2 hb0 hc1.1 (by omega)
  next hl2 =>
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hl2
  rw [e2, ncu_val] at hl2
  have hb0' : 224 ≤ (cu s p).toNat := by have := mt c1.mpr hl2.2; omega
  split at hr
  next hc =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    exact two _ e2 hb0 hc1.1 (by omega)
  next hc =>
  have hc2 : 128 ≤ (cu s (p + ix 1 + ix 1)).toNat ∧ (cu s (p + ix 1 + ix 1)).toNat < 192 := by
    rw [isCont_eq] at hc; simpa using hc
  split at hr
  next hl3 =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    exact three _ e3 hb0 hc1.1 hc2.1 (by omega)
  next hl3 =>
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hl3
  rw [e3, ncu_val] at hl3
  split at hr
  next hc =>
    simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    exact three _ e3 hb0 hc1.1 hc2.1 (by omega)
  next hc =>
  have hc3 : 128 ≤ (cu s (p + ix 1 + ix 1 + ix 1)).toNat ∧ (cu s (p + ix 1 + ix 1 + ix 1)).toNat < 192 := by
    rw [isCont_eq] at hc; simpa using hc
  simp only [Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
  have hw := wc4 (cu s p) (cu s (p + ix 1)) (cu s (p + ix 1 + ix 1)) (cu s (p + ix 1 + ix 1 + ix 1))
    hc1.1 hc2.1 hc3.1
  refine ⟨4, e4, by omega, by omega, ?_, .inr ⟨by rw [hw]; simp, ?_⟩⟩
  · rw [hw, dt _ _ _ (by omega), dt _ _ _ (by omega), dt _ _ _ (by omega), dt _ _ _ (by omega), cu_eq, hB1,
      hB2, hB3]; simp
  · rw [hw]; intro x hx; simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact le80 (by omega)
    · exact le80 hc1.1
    · exact le80 hc2.1
    · exact le80 hc3.1

/-- `collectFrom` with the iteration function as a parameter. Its equation lemmas
never unfold `iterate`; the kernel's whnf of `iterate s p` on a symbolic state does
not terminate in practice, so `collectFrom`'s own equation lemmas cannot be built. -/
def iterList (g : JInt64 → Option (UInt32 × JInt64)) : Nat → JInt64 → List (UInt32 × JInt64)
  | 0, _ => []
  | k + 1, i =>
    collectFrom.match_1 (motive := fun _ => List (UInt32 × JInt64)) (g i) (fun _ => [])
      (fun c j => (c, i) :: iterList g k j)

section
attribute [local irreducible] iterate
set_option smartUnfolding false in
theorem collectFrom_eq_iterList (s : JStr) (k : Nat) (p : JInt64) :
    collectFrom s k p = iterList (iterate s) k p := rfl
end

theorem iterList_none (g : JInt64 → Option (UInt32 × JInt64)) (k : Nat) (p : JInt64)
    (h : g p = none) : iterList g (k + 1) p = [] := by
  simp only [iterList, h]

theorem iterList_some (g : JInt64 → Option (UInt32 × JInt64)) (k : Nat) (p : JInt64)
    (c : UInt32) (j : JInt64) (h : g p = some (c, j)) :
    iterList g (k + 1) p = (c, p) :: iterList g k j := by
  simp only [iterList, h]

theorem collectFrom_none (s : JStr) (k : Nat) (p : JInt64) (h : iterate s p = none) :
    collectFrom s (k + 1) p = [] :=
  (collectFrom_eq_iterList s (k + 1) p).trans (iterList_none (iterate s) k p h)

theorem collectFrom_some (s : JStr) (k : Nat) (p : JInt64) (c : UInt32) (j : JInt64)
    (h : iterate s p = some (c, j)) : collectFrom s (k + 1) p = (c, p) :: collectFrom s k j :=
  (collectFrom_eq_iterList s (k + 1) p).trans ((iterList_some (iterate s) k p c j h).trans
    (congrArg (List.cons (c, p)) (collectFrom_eq_iterList s k j).symm))

theorem dd (L : List UInt8) (a b : Nat) : (L.drop a).drop b = L.drop (a + b) := by
  simp [List.drop_drop, Nat.add_comm]

theorem collect_bytes (s : JStr) (k : Nat) : ∀ (p : JInt64), 1 ≤ p.val → p.val ≤ s.bytes.length + 1 →
    s.bytes.length + 1 - p.val < k →
    ((collectFrom s k p).map (·.1)).flatMap writeChar = s.bytes.drop (p.val.toNat - 1) ∧
      ∀ c ∈ (collectFrom s k p).map (·.1), GoodChar c := by
  induction k with
  | zero => intro p _ _ hk; omega
  | succ k ih =>
    intro p h1 h2 hk
    by_cases hend : p.val = s.bytes.length + 1
    · have hn : collectFrom s (k + 1) p = [] := collectFrom_none s k p (iterate_end s p hend)
      rw [hn]
      refine ⟨?_, by simp⟩
      simp only [List.map_nil, List.flatMap_nil]
      have hq : s.bytes.length ≤ p.val.toNat - 1 := by omega
      exact (List.drop_eq_nil_of_le hq).symm
    · have hp : p.val ≤ s.bytes.length := by omega
      obtain ⟨c, j, hit, m, hj, hm1, hm2, hw, hg⟩ := iterate_step s p h1 hp
      have hc : collectFrom s (k + 1) p = (c, p) :: collectFrom s k j := collectFrom_some s k p c j hit
      have j1 : 1 ≤ j.val := by omega
      have j2 : j.val ≤ s.bytes.length + 1 := by omega
      have j3 : s.bytes.length + 1 - j.val < k := by omega
      obtain ⟨ih1, ih2⟩ := ih j j1 j2 j3
      rw [hc]
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.flatMap_cons]
        rw [ih1, hw]
        have hq : j.val.toNat - 1 = (p.val.toNat - 1) + m := by omega
        rw [hq, ← dd, List.take_append_drop]
      · intro x hx
        simp only [List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hg
        · exact ih2 x hx

theorem chars_spec (s : JStr) : (chars s).flatMap writeChar = s.bytes ∧ ∀ c ∈ chars s, GoodChar c := by
  have hs := ncu_small s
  have e1 : (ix 1).val = 1 := rfl
  have h := collect_bytes s (s.bytes.length + 1) (ix 1) (by rw [e1]; decide) (by rw [e1]; omega)
    (by rw [e1]; omega)
  rw [e1] at h
  simpa [chars, collectPairs] using h

end JuliaLean.Show
