import JuliaLean.Core
import JuliaLean.IntArith.PowersDigits
import JuliaLean.ParsePrint.Bits

/-!
Integer to string and digit functions of `base/intfuncs.jl` at master
`bbfa0ce4150`: `string(n; base, pad)` with its `bin`/`oct`/`dec`/`hex`/`_base`
writers (lines 878-1119), `digits`/`digits!` (1207-1281) and `bitstring`
(1140-1167). Digit counts reuse `JuliaLean.IntArith.PowersDigits`.

Strings are lists of bytes. The writers fill a buffer of `n` bytes by index, as
Julia does with `unsafe_store!`; the buffer starts as zero bytes (Julia's
`_string_n` leaves it uninitialized, but every writer stores every index).

Arithmetic that cannot wrap is exact `Int` arithmetic, each time with the
reason: `_base` and `digits!` only divide by a base of magnitude at least two
(after Julia's promotion of the operands), which can neither overflow nor
change sign. The `string` writers for bases 2, 8, 10, 16 and `bitstring`
use the source's unsigned bit operations.

`digits` is modelled for an `Int` base (`digits(n; base::Int)`, element type
`Int`), Julia's default, with `n` of any `BitInteger` type.

Changes from 1.13.2: `string` clamps the pad with mixed-type `min`/`max`, which
throw `InexactError` for a `UInt64`/`UInt128` pad in 1.13.2; `hex` counts its
digits as `(top_set_bit(x) + 3) ÷ 4` instead of `2sizeof(x) - leading_zeros(x) >> 2`
(equal for these types); writers use `unsafe_store!` instead of `StringMemory`.
-/

namespace JuliaLean.ParsePrint.IntPrint

open JuliaLean JuliaLean.ParsePrint JuliaLean.IntArith.PowersDigits

/-- A byte buffer with one-based indices. -/
abbrev Buf := List Nat

/-- `unsafe_store!(p, v, i)`. -/
def store (b : Buf) (i : Int) (v : Nat) : Buf := b.set (i - 1).toNat v

/-- `_string_n(n)`. -/
def newBuf (n : Int) : Buf := List.replicate n.toNat 0

def chMinus : Nat := 45

/-- `bin` loop storing four digits per step, `base/intfuncs.jl:885-894`. -/
def binLoop4 {t : IntTy} : Nat → Buf × JInt t × Int → Buf × JInt t × Int
  | 0, s => s
  | f+1, (buf, x, i) =>
    if i ≥ 4 then
      let b : JInt .u32 := JInt.rem .u32 (JInt.rem .u8 x)
      let d := JInt.lit .u32 0x30303030 +
        band (shr (b * JInt.lit .u32 0x08040201) 3) (JInt.lit .u32 0x01010101)
      let buf := store buf (i - 3) (JInt.rem .u8 d).val.toNat
      let buf := store buf (i - 2) (JInt.rem .u8 (shr d 8)).val.toNat
      let buf := store buf (i - 1) (JInt.rem .u8 (shr d 16)).val.toNat
      let buf := store buf i (JInt.rem .u8 (shr d 24)).val.toNat
      binLoop4 f (buf, shr x 4, i - 4)
    else (buf, x, i)

/-- `bin` loop storing one digit per step, `base/intfuncs.jl:895-899`. -/
def binLoop1 {t : IntTy} (neg : Bool) : Nat → Buf × JInt t × Int → Buf × JInt t × Int
  | 0, s => s
  | f+1, (buf, x, i) =>
    if i > (if neg then 1 else 0) then
      let buf := store buf i (48 + Nat.land (JInt.rem .u8 x).val.toNat 1)
      binLoop1 neg f (buf, shr x 1, i - 1)
    else (buf, x, i)

/-- The final `neg && unsafe_store!(p, 0x2d, 1)` of every writer. -/
def signed (neg : Bool) (buf : Buf) : Buf := if neg then store buf 1 chMinus else buf

/-- `bin(x::Unsigned, pad, neg)`, `base/intfuncs.jl:878-903`. -/
def bin {t : IntTy} (x : JInt t) (pad : Int) (neg : Bool) : Buf :=
  let m : Int := topSetBit x
  let n := (if neg then 1 else 0) + max pad m
  let (buf, x, i) := binLoop4 (n.toNat / 4 + 1) (newBuf n, x, n)
  let (buf, _, _) := binLoop1 neg (n.toNat + 1) (buf, x, i)
  signed neg buf

/-- `oct` loop, `base/intfuncs.jl:912-916`. -/
def octLoop {t : IntTy} (neg : Bool) : Nat → Buf × JInt t × Int → Buf
  | 0, (buf, _, _) => buf
  | f+1, (buf, x, i) =>
    if i > (if neg then 1 else 0) then
      octLoop neg f (store buf i (48 + Nat.land (JInt.rem .u8 x).val.toNat 7), shr x 3, i - 1)
    else buf

/-- `oct(x::Unsigned, pad, neg)`, `base/intfuncs.jl:905-920`. -/
def oct {t : IntTy} (x : JInt t) (pad : Int) (neg : Bool) : Buf :=
  let m : Int := (topSetBit x + 2) / 3
  let n := (if neg then 1 else 0) + max pad m
  signed neg (octLoop neg (n.toNat + 1) (newBuf n, x, n))

/-- The two characters of `_dec_d100[1 + s]`, `base/intfuncs.jl:923-936`: the
tens digit in the low byte, the ones digit in the high byte. -/
def d100lo (s : Nat) : Nat := 48 + s / 10
def d100hi (s : Nat) : Nat := 48 + s % 10

/-- `dec` loop over nine-digit chunks of a value above `typemax(UInt)`,
`base/intfuncs.jl:989-1002`. -/
def decChunkLoop {t : IntTy} : Nat → Buf × JInt t × Int → Buf × JInt t × Int
  | 0, s => s
  | f+1, (buf, x, i) =>
    if i > 9 ∧ x.val > IntTy.max .u64 then
      let d := udivLit x 1000000000
      let r := x - d * JInt.lit t 1000000000
      let r32 : Nat := (JInt.rem .u32 r).val.toNat
      let (buf, r32) := (List.range 4).foldl (fun (acc : Buf × Nat) (j : Nat) =>
        let (buf, r32) := acc
        let q := r32 / 100
        let s := r32 % 100
        let buf := store buf (i - 2 * (j : Int)) (d100hi s)
        (store buf (i - 2 * (j : Int) - 1) (d100lo s), q)) (buf, r32)
      decChunkLoop f (store buf (i - 8) (48 + r32 % 256), d, i - 9)
    else (buf, x, i)

/-- `dec` loop over two-digit pairs, `base/intfuncs.jl:1004-1011`. -/
def decPairLoop : Nat → Buf × JInt .u64 × Int → Buf × JInt .u64 × Int
  | 0, s => s
  | f+1, (buf, y, i) =>
    if i ≥ 2 then
      let d := udivLit y 100
      let r := (y - d * JInt.lit .u64 100).val.toNat
      decPairLoop f (store (store buf i (d100hi r)) (i - 1) (d100lo r), d, i - 2)
    else (buf, y, i)

/-- `dec(x::Unsigned, pad, neg)`, `base/intfuncs.jl:983-1018`; the digit count is
`ndigits(x, pad=pad)`, and `pad` is an `Int`. -/
def dec {t : IntTy} (x : JInt t) (pad : JInt .i64) (neg : Bool) : Jl Buf := do
  let nd ← ndigits x (JInt.lit .i64 10) pad
  let n : Int := (if neg then 1 else 0) + nd.val
  let (buf, x, i) := decChunkLoop (n.toNat / 9 + 1) (newBuf n, x, n)
  let y : JInt .u64 := JInt.rem .u64 x
  let (buf, y, i) := decPairLoop (n.toNat / 2 + 1) (buf, y, i)
  let buf := if i > (if neg then 1 else 0) then store buf i (48 + (y.val.toNat % 10) % 256) else buf
  pure (signed neg buf)

/-- A hexadecimal digit character, `d + ifelse(d > 0x9, 0x57, 0x30)`. -/
def hexChar (d : Nat) : Nat := d + if d > 9 then 0x57 else 0x30

/-- `hex` loop, `base/intfuncs.jl:1027-1034`. -/
def hexLoop {t : IntTy} : Nat → Buf × JInt t × Int → Buf × JInt t × Int
  | 0, s => s
  | f+1, (buf, x, i) =>
    if i ≥ 2 then
      let b := (JInt.rem .u8 x).val.toNat
      let buf := store buf (i - 1) (hexChar (b / 16))
      let buf := store buf i (hexChar (b % 16))
      hexLoop f (buf, shr x 8, i - 2)
    else (buf, x, i)

/-- `hex(x::Unsigned, pad, neg)`, `base/intfuncs.jl:1020-1042`. -/
def hex {t : IntTy} (x : JInt t) (pad : Int) (neg : Bool) : Buf :=
  let m : Int := (topSetBit x + 3) / 4
  let n := (if neg then 1 else 0) + max pad m
  let (buf, x, i) := hexLoop (n.toNat / 2 + 1) (newBuf n, x, n)
  let buf := if i > (if neg then 1 else 0) then
      store buf i (hexChar (Nat.land (JInt.rem .u8 x).val.toNat 15)) else buf
  signed neg buf

/-- `base36digits` and `base62digits`, `base/intfuncs.jl:1044-1045`, at a zero-based index. -/
def digitChar (big : Bool) (k : Nat) : Nat :=
  if k < 10 then 48 + k
  else if big then (if k < 36 then 65 + (k - 10) else 97 + (k - 36))
  else 97 + (k - 10)

/-- `_base` digit loop, `base/intfuncs.jl:1057-1066`. `rem`/`div`/`mod`/`cld` by
`b` with `abs(b) ≥ 2` are exact after promotion. -/
def baseLoop (b : Int) (big : Bool) (neg : Bool) : Nat → Buf × Int × Int → Buf
  | 0, (buf, _, _) => buf
  | f+1, (buf, x, i) =>
    if i > (if neg then 1 else 0) then
      if b > 0 then baseLoop b big neg f (store buf i (digitChar big (x.tmod b).toNat), x.tdiv b, i - 1)
      else
        -- `cld(x, b) = -fld(x, -b)`
        baseLoop b big neg f (store buf i (digitChar big (x % (-b)).toNat), -(x / (-b)), i - 1)
    else buf

/-- `_base(base, x, pad, neg)`, `base/intfuncs.jl:1047-1070`, for `base::JInt bty`. -/
def base_ {t bty : IntTy} (base : JInt bty) (x : JInt t) (pad : JInt .i64) (neg : Bool) : Jl Buf := do
  if ¬ (x.val ≥ 0 ∨ base.val < 0) then
    .error (.domainError "For negative `x`, `base` must be negative.")
  let ab : JInt bty := if base.val < 0 then -base else base
  if ¬ (2 ≤ ab.val ∧ ab.val ≤ 62) then .error (.domainError "base must satisfy 2 ≤ abs(base) ≤ 62")
  let b : JInt .i64 := JInt.rem .i64 base
  let big := decide (b.val.natAbs > 36)
  let nd ← ndigits x b pad
  let n : Int := (if neg then 1 else 0) + nd.val
  pure (signed neg (baseLoop b.val big neg (n.toNat + 1) (newBuf n, x.val, n)))

/-- `split_sign(n)`, `base/intfuncs.jl:1072-1073`: `unsigned(abs(n))` wraps for `typemin`. -/
def splitSign {t : IntTy} (n : JInt t) : JInt t.toUnsigned × Bool :=
  (JInt.rem t.toUnsigned (if n.val < 0 then -n else n), decide (n.val < 0))

/-- `string(n::Integer; base::Integer, pad::Integer)`, `base/intfuncs.jl:1101-1119`.
The pad is clamped into `Int` (line 1103). -/
def string {t bty : IntTy} (n : JInt t) (base : JInt bty) (pad : Int := 1) : Jl Buf := do
  let pad : JInt .i64 := JInt.wrap .i64 (min (max pad (IntTy.min .i64)) (IntTy.max .i64))
  let (np, neg) := splitSign n
  if base.val = 2 then pure (bin np pad.val neg)
  else if base.val = 8 then pure (oct np pad.val neg)
  else if base.val = 10 then dec np pad neg
  else if base.val = 16 then pure (hex np pad.val neg)
  else if base.val > 0 then base_ base np pad (decide (n.val < 0))
  else do
    -- `convert(Signed, n)`
    let s ← JInt.convert t.toSigned n.val
    base_ base s pad false

/-- `bitstring(x)` for `x::BitInteger`, `base/intfuncs.jl:1140-1167`: the
widths are multiples of four, so only the four-bit loop runs. -/
def bitstring {t : IntTy} (x : JInt t) : Buf :=
  let (buf, _, _) := binLoop4 (t.bits / 4 + 1) (newBuf t.bits, JInt.rem t.toUnsigned x, (t.bits : Int))
  buf

/-! ### `digits` -/

/-- The power-of-two loop of `digits!`, `base/intfuncs.jl:1260-1262`:
`(n >> (k*(i-1))) & c` for `n ≥ 0`. -/
def pow2Digits (n : Int) (k : Nat) (L : Nat) : List Int :=
  (List.range L).map fun i => (n / 2 ^ (k * i)) % 2 ^ k

/-- The `divrem` loop of `digits!`, `base/intfuncs.jl:1264-1267`; truncated division. -/
def divremDigits (b : Int) : Nat → Int → List Int
  | 0, _ => []
  | L+1, n => n.tmod b :: divremDigits b L (n.tdiv b)

/-- The negative-base loop of `digits!` after its first iteration,
`base/intfuncs.jl:1274-1278`: `n, d = fldmod(n, -base); a[i] = d; n = -n`. -/
def negDigits (b : Int) : Nat → Int → List Int
  | 0, _ => []
  | L+1, n => n % (-b) :: negDigits b L (-(n / (-b)))

/-- `digits!(a, n; base)` for `a::Vector{Int}` of length `L`, `base/intfuncs.jl:1249-1281`.
`abs(base)` wraps for `typemin(Int)`. -/
def digitsFill {t : IntTy} (L : Nat) (n : JInt t) (base : JInt .i64) : Jl (List Int) :=
  let ab := if base.val < 0 then -base else base
  if ¬ 2 ≤ ab.val then .error (.domainError "base must be ≥ 2 or ≤ -2")
  else if L = 0 then pure []
  else if base.val > 0 then
    if ispow2 base ∧ n.val ≥ 0 then pure (pow2Digits n.val (trailingZeros base) L)
    else pure (divremDigits base.val L n.val)
  else
    -- the peeled first iteration: `n, d = fldmod(n, -base); a[1] = d; n = -signed(n)`
    let b := base.val
    pure (n.val % (-b) :: negDigits b (L - 1) (-(n.val / (-b))))

/-- `digits(n; base::Int, pad)`, `base/intfuncs.jl:1207-1212`. -/
def digits {t : IntTy} (n : JInt t) (base : JInt .i64) (pad : JInt .i64 := JInt.lit .i64 1) :
    Jl (List Int) := do
  let L ← ndigits n base pad
  digitsFill L.val.toNat n base

end JuliaLean.ParsePrint.IntPrint
