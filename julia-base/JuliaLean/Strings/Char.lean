import JuliaLean.Strings.Basic

/-!
# `Char` encoding, `base/char.jl`

A `Char` is its `UInt32` bit pattern (`bitcast(UInt32, c)`): the UTF-8 bytes
left-aligned, so `'a'` is `0x61000000` and `'é'` is `0xc3a90000`.
-/

namespace JuliaLean.Strings

/-- `leading_zeros(x::UInt32)`. -/
def clz32 (x : UInt32) : Nat := if x = 0 then 32 else 31 - Nat.log2 x.toNat

/-- `leading_ones(x) = leading_zeros(~x)`. -/
def clo32 (x : UInt32) : Nat := clz32 (~~~x)

def ctzAux (x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if x % 2 = 1 then 0 else 1 + ctzAux (x / 2) k

/-- `trailing_zeros(x::UInt32)`. -/
def ctz32 (x : UInt32) : Nat := if x = 0 then 32 else ctzAux x.toNat 32

/-- `x >> k` for `x::UInt32` and `k ≥ 0`: Julia yields `0` once `k ≥ 32`. -/
def ushr32 (x : UInt32) (k : Nat) : UInt32 := if k < 32 then x >>> k.toUInt32 else 0

/-- `bswap(x::UInt32)`. -/
def bswap32 (x : UInt32) : UInt32 :=
  ((x &&& 0xff) <<< 24) ||| (((x >>> 8) &&& 0xff) <<< 16) |||
    (((x >>> 16) &&& 0xff) <<< 8) ||| (x >>> 24)

/-- `x & 56` on a small nonnegative `Int`. -/
def land56 (x : Nat) : Nat := Nat.land x 56

/-- `ismalformed(c::Char)`, `base/char.jl:111-117`. `l1` and `t0` are `Int`. -/
def ismalformed (c : UInt32) : Bool :=
  let l1 := ix (Int.ofNat (clo32 c) * 8)
  let t0 := land56 (ctz32 c)
  decide (l1.val = 8) || decide ((l1 + ix t0).val > 32) ||
    (ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) t0 != 0)

/-- `is_overlong_enc(u)`, `base/char.jl:119`. -/
def isOverlongEnc (u : UInt32) : Bool :=
  (u >>> 25 == 0x60) || (u >>> 21 == 0x0704) || (u >>> 20 == 0x0f08)

/-- `isoverlong(c::Char)`, `base/char.jl:121-124`. -/
def isoverlong (c : UInt32) : Bool := isOverlongEnc c

/-- `UInt32(c::Char)`, `base/char.jl:158-171`; `codepoint(c) = UInt32(c)` (`:100`). -/
def codepoint (c : UInt32) : SJl UInt32 :=
  let u := c
  if u < 0x80000000 then .ok (u >>> 24)
  else
    let l1 := clo32 u
    let t0 := land56 (ctz32 u)
    if decide (l1 = 1) || decide ((ix (8 * Int.ofNat l1) + ix t0).val > 32) ||
        (ushr32 ((u &&& 0x00c0c0c0) ^^^ 0x00808080) t0 != 0) then .error (.invalidChar c)
    else
      let u := u &&& ushr32 0xffffffff l1
      let u := ushr32 u t0
      .ok (((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
        ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6))

/-- `Char(u::UInt32)`, `base/char.jl:211-220`. -/
def charOfU32 (u : UInt32) : SJl UInt32 :=
  if u < 0x80 then .ok (u <<< 24)
  else if !decide (u < 0x00200000) then .error (.codePointError u)
  else
    let c : UInt32 := ((u <<< (0 : UInt32)) &&& (0x0000003f : UInt32)) |||
      ((u <<< (2 : UInt32)) &&& (0x00003f00 : UInt32)) |||
      ((u <<< (4 : UInt32)) &&& (0x003f0000 : UInt32)) |||
      ((u <<< (6 : UInt32)) &&& (0x3f000000 : UInt32))
    .ok (if u < 0x00000800 then (c <<< (16 : UInt32)) ||| (0xc0800000 : UInt32)
      else if u < 0x00010000 then (c <<< (8 : UInt32)) ||| (0xe0808000 : UInt32)
      else c ||| (0xf0808080 : UInt32))

/-- `isvalid(c::AbstractChar)`, `base/strings/unicode.jl:58`, with Char `≤` the
bit-pattern comparison (`base/char.jl:264`): `'\ud7ff'` is `0xed9fbf00`,
`'\ue000'` is `0xee808000`, `'\U10ffff'` is `0xf48fbfbf`. -/
def isvalidChar (c : UInt32) : Bool :=
  !ismalformed c && !isoverlong c &&
    (decide (c ≤ 0xed9fbf00) || (decide (0xee808000 ≤ c) && decide (c ≤ 0xf48fbfbf)))

/-- `ncodeunits(c::Char)`, `base/char.jl:71-78`. -/
def ncodeunitsChar (c : UInt32) : Nat :=
  4 - ctz32 c / 8 + (if c = 0 then 1 else 0)

/-- The bytes `__unsafe_string!(out, c, offs)` stores, `base/strings/substring.jl:215-231`:
the low bytes of `bswap(c)` in order, `ncodeunits(c)` of them. -/
def charBytes (c : UInt32) : List UInt8 :=
  let x := bswap32 c
  [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8].take (ncodeunitsChar c)

/-- `isascii(c::Char) = bswap(reinterpret(UInt32, c)) < 0x80`, `base/strings/basic.jl:618`. -/
def isasciiChar (c : UInt32) : Bool := decide (bswap32 c < 0x80)

/-- `string(cs::Char...)` = `_string`, `base/strings/substring.jl:256-283`: the
total size is the sum of `ncodeunits`, then each char's bytes are stored. -/
def stringOfChars (cs : List UInt32) : SJl JStr :=
  let bs := cs.flatMap charBytes
  if h : bs.length < 2 ^ 62 then .ok ⟨bs, h⟩ else .error .outOfMemory

end JuliaLean.Strings
