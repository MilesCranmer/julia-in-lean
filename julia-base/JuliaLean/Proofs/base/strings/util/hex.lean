import JuliaLean.base.strings.util
import JuliaLean.Proofs.base.strings.string.length
import JuliaLean.Registry.Types

/-!
# `hex2bytes` and `bytes2hex`, `base/strings/util.jl:1192-1334`

Master `bbfa0ce4150`. A byte vector is a `List UInt8`. The generic
`hex2bytes!(dest, itr)` is modelled once over an iteration protocol
(`iterate(itr)` and `iterate(itr, state)`) and an element conversion
(`number_from_hex`), and instantiated for `codeunits(s::String)` and for
`SubString{String}`.
-/

namespace JuliaLean.StringUtil

open JuliaLean.Strings JuliaLean.Registry

/-! ## Byte tables -/

/-- `y` is one of `0-9a-f`. -/
def isHexLower (y : UInt8) : Bool := (decide (0x30 ≤ y) && decide (y ≤ 0x39)) ||
  (decide (0x61 ≤ y) && decide (y ≤ 0x66))

/-- Per-byte facts: both digits convert back, recombine to the byte, and are
lowercase hex digits. -/
def hexByteOk (x : UInt8) : Bool :=
  okSat (· == x >>> 4) (numberFromHexByte (hexHi x)) &&
  okSat (· == x &&& 0xf) (numberFromHexByte (hexLo x)) &&
  (((x >>> 4) <<< 4) + (x &&& 0xf) == x) && isHexLower (hexHi x) && isHexLower (hexLo x)

set_option maxRecDepth 100000 in
theorem hexByteOk_table : ∀ n : Fin 256, hexByteOk (UInt8.ofNat n.val) = true := by decide

theorem hexByteOk_all (x : UInt8) : hexByteOk x = true := by
  have h := hexByteOk_table ⟨x.toNat, UInt8.toNat_lt x⟩
  simpa [UInt8.ofNat_toNat] using h

theorem nfh_hi (x : UInt8) : numberFromHexByte (hexHi x) = .ok (x >>> 4) := by
  have h := hexByteOk_all x
  simp only [hexByteOk, Bool.and_eq_true] at h
  exact of_okSat_eq _ _ h.1.1.1.1

theorem nfh_lo (x : UInt8) : numberFromHexByte (hexLo x) = .ok (x &&& 0xf) := by
  have h := hexByteOk_all x
  simp only [hexByteOk, Bool.and_eq_true] at h
  exact of_okSat_eq _ _ h.1.1.1.2

theorem recombine (x : UInt8) : ((x >>> 4) <<< 4) + (x &&& 0xf) = x := by
  have h := hexByteOk_all x
  simp only [hexByteOk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem hexHi_lower (x : UInt8) : isHexLower (hexHi x) = true := by
  have h := hexByteOk_all x
  simp only [hexByteOk, Bool.and_eq_true] at h
  exact h.1.2

theorem hexLo_lower (x : UInt8) : isHexLower (hexLo x) = true := by
  have h := hexByteOk_all x
  simp only [hexByteOk, Bool.and_eq_true] at h
  exact h.2

theorem isHexLower_iff (y : UInt8) :
    isHexLower y = true ↔ (0x30 ≤ y ∧ y ≤ 0x39) ∨ (0x61 ≤ y ∧ y ≤ 0x66) := by
  simp [isHexLower]

theorem isHexLower_ascii (y : UInt8) (h : isHexLower y = true) : y.toNat < 128 := by
  rw [isHexLower_iff] at h
  simp only [UInt8.le_iff_toNat_le] at h
  have : (0x39 : UInt8).toNat = 57 := rfl
  have : (0x66 : UInt8).toNat = 102 := rfl
  omega

theorem fill_length (b : List UInt8) : (bytes2hexFill b).length = 2 * b.length := by
  induction b with
  | nil => rfl
  | cons x b ih =>
    simp only [bytes2hexFill, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem fill_lower (b : List UInt8) : ∀ y ∈ bytes2hexFill b, isHexLower y = true := by
  intro y hy
  simp only [bytes2hexFill, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hy
  obtain ⟨x, _, hx⟩ := hy
  rcases hx with h | h <;> subst h
  · exact hexHi_lower x
  · exact hexLo_lower x

/-! ## `length` of an ASCII string -/

theorem getD_ascii (l : List UInt8) (n : Nat) (h : ∀ x ∈ l, x.toNat < 128) :
    (l.getD n 0).toNat < 128 := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[n]? with
  | none => simp
  | some x => simp only [Option.getD_some]; exact h x (List.mem_of_getElem? hx)

theorem absCnt_ascii (s : JStr) (hs : ∀ x ∈ s.bytes, x.toNat < 128) :
    ∀ (k : Nat) (p : Int), absCnt s k p = 0 := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    have hb : bv s p < 128 := getD_ascii s.bytes _ hs
    have hn : ¬ thisZ s p < p := by rw [thisZ_noncont s p (by omega)]; omega
    simp only [absCnt, if_neg hn, ih]

/-- An ASCII string has one character per byte. -/
theorem length_ascii (s : JStr) (hs : ∀ x ∈ s.bytes, x.toNat < 128) :
    (length s).val = s.bytes.length := by
  have hsm := ncu_small s
  rw [length_validIndices]
  unfold validIndices
  have hv := validFrom_absCnt s s.bytes.length (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega)
  rw [absCnt_ascii s hs] at hv
  omega

/-! ## Round trip -/

theorem cuIt_cons (x : UInt8) (r : List UInt8) : cuIt (x :: r) = some (x, r) := rfl

theorem hexLoop_fill (b : List UInt8) :
    hexLoop (fun st => .ok (cuIt st)) numberFromHexByte b.length (cuIt (bytes2hexFill b)) =
      .ok b := by
  induction b with
  | nil => rfl
  | cons x b ih =>
    have e : bytes2hexFill (x :: b) = hexHi x :: hexLo x :: bytes2hexFill b := rfl
    rw [e, List.length_cons]
    simp only [hexLoop, cuIt_cons]
    rw [nfh_hi, nfh_lo]
    simp only
    rw [ih, recombine]
    rfl

theorem bytes2hex_ok (b : List UInt8) (hb : b.length < 2 ^ 61) :
    ∃ h : JStr, bytes2hex b = .ok h ∧ h.bytes = bytes2hexFill b := by
  have hl := fill_length b
  have e : (ix 2 * ix (b.length : Int)).val = 2 * (b.length : Int) := by
    show (JInt.wrap .i64 ((ix 2).val * (ix (b.length : Int)).val)).val = _
    rw [ix2, ix_val _ (by omega) (by omega)]
    exact wrap64_val _ (by omega) (by omega)
  refine ⟨⟨bytes2hexFill b, by omega⟩, ?_, rfl⟩
  unfold bytes2hex stringN
  simp only [e]
  rw [if_neg (by omega), if_pos (by omega), dif_pos (by omega)]

theorem shr1_val (x : JInt64) (h : 0 ≤ x.val) : (shr1 x).val = x.val / 2 := by
  have := x.property.2
  simp only [IntTy.max, IntTy.signed, IntTy.bits] at this
  exact wrap64_val _ (by omega) (by simp at this; omega)

theorem hex2bytes_fill (b : List UInt8) (h : JStr) (hh : h.bytes = bytes2hexFill b) :
    hex2bytes h = .ok b := by
  have hsm := ncu_small h
  have hlen : h.bytes.length = 2 * b.length := by rw [hh, fill_length]
  have hasc : ∀ x ∈ h.bytes, x.toNat < 128 := by
    rw [hh]; intro x hx; exact isHexLower_ascii x (fill_lower b x hx)
  have e1 : (ncodeunits h).val = 2 * (b.length : Int) := by rw [ncu_val, hlen]; omega
  have e2 : (length h).val = 2 * (b.length : Int) := by rw [length_ascii h hasc, hlen]; omega
  have e3 : (shr1 (length h)).val = b.length := by rw [shr1_val _ (by omega), e2]; omega
  have e4 : (ix 2 * shr1 (length h)).val = 2 * (b.length : Int) := by
    show (JInt.wrap .i64 ((ix 2).val * (shr1 (length h)).val)).val = _
    rw [ix2, e3]
    exact wrap64_val _ (by omega) (by omega)
  unfold hex2bytes hex2bytesBang
  rw [if_neg (by rw [e1, e2]; simp), if_neg (by rw [e1]; omega), if_neg (by rw [e4, e1]; simp)]
  by_cases hb : b.length = 0
  · rw [if_pos (by rw [e1]; omega), List.eq_nil_of_length_eq_zero hb]
  · rw [if_neg (by rw [e1]; omega)]
    simp only
    rw [show (shr1 (length h)).val.toNat = b.length by omega, hh]
    exact hexLoop_fill b

/-! ## Properties -/

/-- `hex2bytes(bytes2hex(b)) == b` for every byte vector `b`, through the String
method of `hex2bytes`. Julia vectors are shorter than `2^61` bytes (the hex string
has `2 * length(b)` bytes and every String is shorter than `2^62`). -/
def HexRoundtrip : Prop :=
  ∀ b : List UInt8, b.length < 2 ^ 61 → ∃ h, bytes2hex b = .ok h ∧ hex2bytes h = .ok b

theorem hexRoundtrip_proven : HexRoundtrip := by
  intro b hb
  obtain ⟨h, hok, hh⟩ := bytes2hex_ok b hb
  exact ⟨h, hok, hex2bytes_fill b h hh⟩

/-- `bytes2hex(b)` has `2 * length(b)` bytes, each one of `0-9a-f`. -/
def Bytes2hexLowercase : Prop :=
  ∀ (b : List UInt8) (h : JStr), bytes2hex b = .ok h →
    h.bytes.length = 2 * b.length ∧
      ∀ y ∈ h.bytes, (0x30 ≤ y ∧ y ≤ 0x39) ∨ (0x61 ≤ y ∧ y ≤ 0x66)

theorem bytes2hexLowercase_proven : Bytes2hexLowercase := by
  intro b h hok
  unfold bytes2hex at hok
  simp only at hok
  split at hok
  · cases hok
  · have hh := stringN_ok hok
    rw [hh]
    exact ⟨fill_length b, fun y hy => (isHexLower_iff y).1 (fill_lower b y hy)⟩

/-- The call succeeded or threw `ArgumentError`. -/
def okOrArgErr {α : Type} : SJl α → Bool
  | .ok _ => true
  | .error (.jl (.argumentError _)) => true
  | .error _ => false

/-- `hex2bytes` on any SubString of any String returns or throws
`ArgumentError`, as the String method does. -/
def Hex2bytesArgError : Prop :=
  ∀ (s : JStr) (i j : JInt64) (ss : JSub), substring s i j = .ok ss → okOrArgErr (hex2bytesSub ss) = true

/-- `"ĀĀ"`: bytes `c4 80 c4 80`. -/
def strAA : JStr := ⟨[0xc4, 0x80, 0xc4, 0x80], by decide⟩

theorem hex2bytesArgError_refuted : ¬ Hex2bytesArgError := by
  intro h
  have := h strAA (ix 1) (ix 3) ⟨strAA, ix 0, ix 4⟩ (of_okSat_eq _ _ (by decide))
  revert this; decide

/-- Registry entries of the hex conversions. -/
def hexEntries : List Entry := []

end JuliaLean.StringUtil
