import JuliaLean.Transcode.Valid

/-!
# Byte tables for the UTF-8 / UTF-16 round trip

For every well-formed UTF-8 character the facts below are checked
exhaustively by the kernel (`decide +kernel`, no native code): which branch
of `transcode(UInt16, ...)` (`u16Loop`) the character takes, the UTF-16 code
units it produces, which branch of `transcode(UInt8, ...)` (`wrLoop`) those
units take, and that the bytes written there are the original bytes.
4-byte characters are split into the part that depends on the first three
bytes (`P4a`) and the part that depends on the last two (`P4b`).
-/

namespace JuliaLean.Transcode

/-- Facts for a 1-byte character. -/
abbrev P1 (a : UInt8) : Prop :=
  wfChar [a] = true →
    isLead a = false ∧ a.toUInt16 < 0x80 ∧
    a.toUInt16.toUInt8 = a ∧ isHigh a.toUInt16 = false ∧ isLow a.toUInt16 = false ∧
    decide (0xf0 ≤ a) = false

/-- Facts for a 2-byte character. -/
abbrev P2 (a b : UInt8) : Prop :=
  wfChar [a, b] = true →
    isLead a = true ∧
    (decide (-64 ≤ sx b) || (a == 0xf4 && decide (0x8f < b))) = false ∧ a < 0xe0 ∧
    ¬ dec2 a b < 0x80 ∧ dec2 a b < 0x800 ∧ enc2 (dec2 a b) = [a, b] ∧
    isHigh (dec2 a b) = false ∧ isLow (dec2 a b) = false ∧
    decide (0xf0 ≤ a) = false ∧ decide (0xf0 ≤ b) = false

/-- The part of `wfChar [a, b, c]` that depends on `a` and `b`. -/
def pre3 (a b : UInt8) : Bool :=
  if a == 0xe0 then 0xa0 ≤ b && b ≤ 0xbf
  else if a == 0xed then 0x80 ≤ b && b ≤ 0x9f
  else 0xe1 ≤ a && a ≤ 0xef && isC b

theorem wfChar3 (a b c : UInt8) : wfChar [a, b, c] = (isC c && pre3 a b) := rfl

/-- Facts for a 3-byte character. -/
abbrev P3 (a b c : UInt8) : Prop :=
  wfChar [a, b, c] = true →
    isLead a = true ∧
    (decide (-64 ≤ sx b) || (a == 0xf4 && decide (0x8f < b))) = false ∧ ¬ a < 0xe0 ∧
    decide (-64 ≤ sx c) = false ∧ a < 0xf0 ∧
    ¬ dec3 a b c < 0x80 ∧ ¬ dec3 a b c < 0x800 ∧ ((dec3 a b c &&& 0xfc00) == 0xd800) = false ∧
    isLow (dec3 a b c) = false ∧ enc3 (dec3 a b c) = [a, b, c] ∧
    decide (0xf0 ≤ a) = false ∧ decide (0xf0 ≤ b) = false ∧ decide (0xf0 ≤ c) = false

/-- The part of `wfChar [a, b, c, d]` that depends on `a` and `b`. -/
def pre4 (a b : UInt8) : Bool :=
  if a == 0xf0 then 0x90 ≤ b && b ≤ 0xbf
  else if a == 0xf4 then 0x80 ≤ b && b ≤ 0x8f
  else 0xf1 ≤ a && a ≤ 0xf3 && isC b

theorem wfChar4 (a b c d : UInt8) : wfChar [a, b, c, d] = (isC c && isC d && pre4 a b) := rfl

/-- Facts for the first three bytes of a 4-byte character: the branch taken and
the high surrogate, whose first two output bytes are `a, b`. -/
abbrev P4a (a b c : UInt8) : Prop :=
  (isC c && pre4 a b) = true →
    isLead a = true ∧
    (decide (-64 ≤ sx b) || (a == 0xf4 && decide (0x8f < b))) = false ∧ ¬ a < 0xe0 ∧
    decide (-64 ≤ sx c) = false ∧ ¬ a < 0xf0 ∧ (a == 0xf0 && b < 0x90) = false ∧
    ¬ dec4hi a b c < 0x80 ∧ ¬ dec4hi a b c < 0x800 ∧ ((dec4hi a b c &&& 0xfc00) == 0xd800) = true ∧
    (0xf0 : UInt8) ||| ((dec4hi a b c + 0x2840) >>> 8).toUInt8 = a ∧
    (0x80 : UInt8) ||| ((dec4hi a b c + 0x2840).toUInt8 >>> 2) = b ∧
    (((dec4hi a b c + 0x2840).toUInt8 <<< 4) &&& (0x3f : UInt8)) = ((c >>> 4) &&& 3) <<< 4 ∧
    decide (0xf0 ≤ a) = true ∧ decide (0xf0 ≤ b) = false ∧ decide (0xf0 ≤ c) = false

/-- Facts for the last two bytes of a 4-byte character: the low surrogate, its
output bytes, and the reassembly of the third byte. -/
abbrev P4b (c d : UInt8) : Prop :=
  (isC c && isC d) = true →
    decide (-64 ≤ sx d) = false ∧ ((dec4lo c d &&& 0xfc00) == 0xdc00) = true ∧
    cont (dec4lo c d).toUInt8 = d ∧ (dec4lo c d >>> 6).toUInt8 = (0x70 : UInt8) ^^^ (c &&& 0xf) ∧
    (0xf0 : UInt8) ^^^ (((c >>> 4) &&& 3) <<< 4) ^^^ ((0x70 : UInt8) ^^^ (c &&& 0xf)) = c ∧
    decide (0xf0 ≤ d) = false

set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
set_option synthInstance.maxHeartbeats 0
set_option maxHeartbeats 0

theorem tab1 : ∀ x, x < 256 → P1 (UInt8.ofNat x) := by decide +kernel

theorem tab2 : ∀ x, x < 256 → ∀ y, y < 256 → P2 (UInt8.ofNat x) (UInt8.ofNat y) := by
  decide +kernel

/-- `f lo && f (lo + 1) && ... && f (lo + n - 1)`. -/
def allFrom (lo : Nat) : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f (lo + n) && allFrom lo n f

theorem allFrom_spec (lo : Nat) : ∀ (n : Nat) (f : Nat → Bool), allFrom lo n f = true →
    ∀ i, lo ≤ i → i < lo + n → f i = true := by
  intro n
  induction n with
  | zero => intro f _ i h1 h2; omega
  | succ n ih =>
    intro f h i h1 h2
    simp only [allFrom, Bool.and_eq_true] at h
    by_cases hi : i = lo + n
    · subst hi; exact h.1
    · exact ih f h.2 i h1 (by omega)

/-- The 3-byte table for lead bytes `lo, ..., lo + n - 1`. -/
def chunk3 (lo n : Nat) : Bool :=
  allFrom lo n fun x => allFrom 0 256 fun y =>
    !pre3 (UInt8.ofNat x) (UInt8.ofNat y) ||
      allFrom 0 256 fun z => decide (P3 (UInt8.ofNat x) (UInt8.ofNat y) (UInt8.ofNat z))

/-- The 4-byte table for lead bytes `lo, ..., lo + n - 1`. -/
def chunk4 (lo n : Nat) : Bool :=
  allFrom lo n fun x => allFrom 0 256 fun y =>
    !pre4 (UInt8.ofNat x) (UInt8.ofNat y) ||
      allFrom 0 256 fun z => decide (P4a (UInt8.ofNat x) (UInt8.ofNat y) (UInt8.ofNat z))

theorem lead3_range : allFrom 0 256 (fun x => allFrom 0 256 fun y =>
    !pre3 (UInt8.ofNat x) (UInt8.ofNat y) || (decide (0xe0 ≤ x) && decide (x < 0xf0))) = true := by
  decide +kernel

theorem lead4_range : allFrom 0 256 (fun x => allFrom 0 256 fun y =>
    !pre4 (UInt8.ofNat x) (UInt8.ofNat y) || (decide (0xf0 ≤ x) && decide (x < 0xf5))) = true := by
  decide +kernel

theorem tab3a : chunk3 0xe0 4 = true := by decide +kernel
theorem tab3b : chunk3 0xe4 4 = true := by decide +kernel
theorem tab3c : chunk3 0xe8 4 = true := by decide +kernel
theorem tab3d : chunk3 0xec 4 = true := by decide +kernel
theorem tab4a1 : chunk4 0xf0 2 = true := by decide +kernel
theorem tab4a2 : chunk4 0xf2 3 = true := by decide +kernel

theorem tab4b : ∀ x, x < 256 → ∀ y, y < 256 → P4b (UInt8.ofNat x) (UInt8.ofNat y) := by
  decide +kernel

theorem facts1 (a : UInt8) : P1 a := by
  have := tab1 a.toNat (UInt8.toNat_lt a); simpa [UInt8.ofNat_toNat] using this

theorem facts2 (a b : UInt8) : P2 a b := by
  have := tab2 a.toNat (UInt8.toNat_lt a) b.toNat (UInt8.toNat_lt b)
  simpa only [UInt8.ofNat_toNat] using this

/-- Look up `a, b, c` in a 3- or 4-byte table whose lead bytes include `a`. -/
theorem chunk_at {lo n : Nat} {pre : UInt8 → UInt8 → Bool} {P : UInt8 → UInt8 → UInt8 → Prop}
    [∀ a b c, Decidable (P a b c)]
    (ht : (allFrom lo n fun x => allFrom 0 256 fun y =>
      !pre (UInt8.ofNat x) (UInt8.ofNat y) ||
        allFrom 0 256 fun z => decide (P (UInt8.ofNat x) (UInt8.ofNat y) (UInt8.ofNat z))) = true)
    (a b c : UInt8) (hp : pre a b = true) (h1 : lo ≤ a.toNat) (h2 : a.toNat < lo + n) : P a b c := by
  have hx := allFrom_spec lo n _ ht a.toNat h1 h2
  have hy := allFrom_spec 0 256 _ hx b.toNat (Nat.zero_le _) (UInt8.toNat_lt b)
  simp only [UInt8.ofNat_toNat, hp, Bool.not_true, Bool.false_or] at hy
  have hz := allFrom_spec 0 256 _ hy c.toNat (Nat.zero_le _) (UInt8.toNat_lt c)
  simp only [UInt8.ofNat_toNat] at hz
  exact of_decide_eq_true hz

theorem lead_at {pre : UInt8 → UInt8 → Bool} {lo hi : Nat}
    (ht : allFrom 0 256 (fun x => allFrom 0 256 fun y =>
      !pre (UInt8.ofNat x) (UInt8.ofNat y) || (decide (lo ≤ x) && decide (x < hi))) = true)
    (a b : UInt8) (hp : pre a b = true) : lo ≤ a.toNat ∧ a.toNat < hi := by
  have hx := allFrom_spec 0 256 _ ht a.toNat (Nat.zero_le _) (UInt8.toNat_lt a)
  have hy := allFrom_spec 0 256 _ hx b.toNat (Nat.zero_le _) (UInt8.toNat_lt b)
  simp only [UInt8.ofNat_toNat, hp, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at hy
  exact hy

theorem facts3 (a b c : UInt8) : P3 a b c := by
  intro h
  have hp : pre3 a b = true := by rw [wfChar3] at h; simp only [Bool.and_eq_true] at h; exact h.2
  have hr := lead_at lead3_range a b hp
  have : P3 a b c := by
    by_cases h1 : a.toNat < 0xe4
    · exact chunk_at (pre := pre3) (P := P3) tab3a a b c hp hr.1 (by omega)
    by_cases h2 : a.toNat < 0xe8
    · exact chunk_at (pre := pre3) (P := P3) tab3b a b c hp (by omega) (by omega)
    by_cases h3 : a.toNat < 0xec
    · exact chunk_at (pre := pre3) (P := P3) tab3c a b c hp (by omega) (by omega)
    · exact chunk_at (pre := pre3) (P := P3) tab3d a b c hp (by omega) (by omega)
  exact this h

theorem facts4a (a b c : UInt8) : P4a a b c := by
  intro h
  have hp : pre4 a b = true := by simp only [Bool.and_eq_true] at h; exact h.2
  have hr := lead_at lead4_range a b hp
  have : P4a a b c := by
    by_cases h1 : a.toNat < 0xf2
    · exact chunk_at (pre := pre4) (P := P4a) tab4a1 a b c hp hr.1 (by omega)
    · exact chunk_at (pre := pre4) (P := P4a) tab4a2 a b c hp (by omega) (by omega)
  exact this h

theorem facts4b (c d : UInt8) : P4b c d := by
  have := tab4b c.toNat (UInt8.toNat_lt c) d.toNat (UInt8.toNat_lt d)
  simpa only [UInt8.ofNat_toNat] using this

end JuliaLean.Transcode
