import JuliaLean.Strings.Length
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

/-- `ArgumentError(msg)`. -/
abbrev argErr (msg : String) : SErr := .jl (.argumentError msg)

/-- `hex_chars`, `base/char.jl:308-311`: `'0'..'9'` then `'a'..'z'`. -/
def hexChars : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
   0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d,
   0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a]

/-- `hex_chars[1 + x >> 4]` (`>>` binds tighter than `+`). -/
def hexHi (x : UInt8) : UInt8 := hexChars.getD (x >>> 4).toNat 0

/-- `hex_chars[1 + x & 0xf]`. -/
def hexLo (x : UInt8) : UInt8 := hexChars.getD (x &&& 0xf).toNat 0

/-- The bytes the loop of `bytes2hex` stores: `hexHi x` at `2i - 1` and
`hexLo x` at `2i` for the `i`-th byte `x` (`base/strings/util.jl:1321-1324`). -/
def bytes2hexFill (b : List UInt8) : List UInt8 := b.flatMap fun x => [hexHi x, hexLo x]

/-- `bytes2hex(itr)` for `itr::Vector{UInt8}`, `base/strings/util.jl:1316-1327`.
The `eltype` check passes. `2*length(itr)` is an `Int` product, and
`_string_n(n)` converts it with `convert(Csize_t, n)` (`base/strings/string.jl:184`),
which throws `InexactError` for negative `n`. -/
def bytes2hex (b : List UInt8) : SJl JStr :=
  let n := ix 2 * ix b.length
  if n.val < 0 then .error (.jl (.inexactError "UInt64"))
  else stringN n.val.toNat fun _ => bytes2hexFill b

/-- `number_from_hex(c::UInt8)`, `base/strings/util.jl:1278-1283`. -/
def numberFromHexByte (c : UInt8) : SJl UInt8 :=
  if 0x30 ≤ c ∧ c ≤ 0x39 then .ok (c - 0x30)
  else
    let c := c ||| 0x20
    if 0x61 ≤ c ∧ c ≤ 0x66 then .ok (c - 0x61 + 0x0a)
    else .error (argErr "byte is not an ASCII hexadecimal digit")

/-- `number_from_hex(c::Char) = number_from_hex(UInt8(c))`, `base/strings/util.jl:1277`.
`UInt8(c)` is `UInt8(codepoint(c))` (`base/char.jl:56`): `codepoint` throws
`InvalidCharError` for a malformed `c`, and the checked conversion of the
`UInt32` throws `InexactError` above `0xff`. -/
def numberFromHexChar (c : UInt32) : SJl UInt8 :=
  match codepoint c with
  | .error e => .error e
  | .ok u => if u ≤ 0xff then numberFromHexByte u.toUInt8 else .error (.jl (.inexactError "UInt8"))

/-- The loop of `hex2bytes!(dest, itr)`, `base/strings/util.jl:1265-1271`, over
`k` remaining entries of `dest`; `next` is the pending `iterate` result. The
`::NTuple{2,Any}` assertions fail (`TypeError`, here `.assertion`) only when
`itr` yields fewer than `2 * length(dest)` elements, which the length checks
before the loop exclude. -/
def hexLoop {α σ : Type} (it : σ → SJl (Option (α × σ))) (conv : α → SJl UInt8) :
    Nat → Option (α × σ) → SJl (List UInt8)
  | 0, _ => .ok []
  | k + 1, next =>
    match next with
    | none => .error .assertion
    | some (x, st) =>
      match it st with
      | .error e => .error e
      | .ok none => .error .assertion
      | .ok (some (y, st)) =>
        match it st with
        | .error e => .error e
        | .ok next =>
          match conv x with
          | .error e => .error e
          | .ok hx =>
            match conv y with
            | .error e => .error e
            | .ok hy => (hexLoop it conv k next).map (fun rest => ((hx <<< 4) + hy) :: rest)

/-- `hex2bytes!(dest, itr)`, `base/strings/util.jl:1260-1274`, with `length(dest) =
destLen` and `length(itr) = len`; `start` is `iterate(itr)`, `it` is
`iterate(itr, state)` and `conv` is `number_from_hex`. The result is the
contents of `dest`; when `len = 0` the checks force `destLen = 0`. -/
def hex2bytesBang {α σ : Type} (destLen len : JInt64) (start : SJl (Option (α × σ)))
    (it : σ → SJl (Option (α × σ))) (conv : α → SJl UInt8) : SJl (List UInt8) :=
  if len.val % 2 ≠ 0 then .error (argErr "length of iterable must be even")
  else if (ix 2 * destLen).val ≠ len.val then
    .error (argErr "length of output array must be half of the length of input iterable")
  else if len.val = 0 then .ok []
  else
    match start with
    | .error e => .error e
    | .ok next => hexLoop it conv destLen.val.toNat next

/-- `x >> 1` for `x::Int`: arithmetic shift, i.e. floor division by 2. -/
def shr1 (x : JInt64) : JInt64 := JInt.wrap .i64 (x.val / 2)

/-- `iterate` over `codeunits(s)` (a byte vector); the state is the list of
remaining bytes. -/
def cuIt (st : List UInt8) : Option (UInt8 × List UInt8) :=
  match st with
  | [] => none
  | x :: rest => some (x, rest)

/-- `hex2bytes(s::String)`: `hex2bytes(s) = hex2bytes!(Vector{UInt8}(undef,
length(s) >> 1), s)` (`base/strings/util.jl:1237`), then the String method
(`:1240-1244`): `sizeof(s) != length(s)` throws, else
`hex2bytes!(dest, transcode(UInt8, s))` with `transcode(UInt8, s) = codeunits(s)`
(`base/strings/cstring.jl:178,163`). -/
def hex2bytes (s : JStr) : SJl (List UInt8) :=
  if (ncodeunits s).val ≠ (length s).val then
    .error (argErr "input string must consist of hexadecimal characters only")
  else
    hex2bytesBang (shr1 (length s)) (ncodeunits s) (.ok (cuIt s.bytes)) (fun st => .ok (cuIt st))
      numberFromHexByte

/-- `hex2bytes(ss::SubString{String})`: `:1237` with `length(ss)`
(`base/strings/substring.jl:144`), then the generic `hex2bytes!` (`:1260-1274`)
iterating the characters (`base/strings/substring.jl:151-158`) and converting
each with `number_from_hex(::Char)`. -/
def hex2bytesSub (ss : JSub) : SJl (List UInt8) :=
  match subLength ss with
  | .error e => .error e
  | .ok len => hex2bytesBang (shr1 len) len (subIterate ss (ix 1)) (subIterate ss) numberFromHexChar

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
