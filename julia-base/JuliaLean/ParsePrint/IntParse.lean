import JuliaLean.Core
import JuliaLean.IntArith.Checked
import JuliaLean.ParsePrint.Bits

/-!
Integer parsing from UTF-8 bytes, `base/parse.jl` and `base/parsers/ints.jl` at
master `bbfa0ce4150`.

A Julia `String` is its list of code units (`Bytes`); index arithmetic on `Int`
indices (`i`, `j`, `k`, `d`, `p`) stays within the string length, so it is
modelled with `Int`. Code units are `UInt8` values and their arithmetic wraps as
in Julia.

The UTF-8 decoding (`iterate`, `getindex`, `thisind`) and `isspace` follow
`base/strings/string.jl:243-271,504-560`, `base/char.jl:111-192` and
`base/strings/unicode.jl:372-382,624-626`. The only Unicode data `isspace`
needs is the set of code points in categories Zs, Zl and Zp (Unicode 16):
U+0020, U+00A0, U+1680, U+2000-U+200A, U+2028, U+2029, U+202F, U+205F, U+3000.

Each `while` loop is recursion on fuel that exceeds the number of iterations:
every iteration advances an index by at least one within the string.

Julia 1.13.2 parses integers with a different, `Char`-based implementation
(`base/parse.jl:51-183` at `v1.13.2`) that this module does not model.
-/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean JuliaLean.ParsePrint

abbrev Byte := JInt .u8
abbrev Bytes := List Byte

/-- `codeunit(s, i)` for an in-bounds one-based index. -/
def cu (s : Bytes) (i : Int) : Byte := s.getD (i - 1).toNat (JInt.lit .u8 0)

/-- The code unit as a natural number. -/
def cuN (s : Bytes) (i : Int) : Nat := (cu s i).val.toNat

/-- `ncodeunits(s)`. -/
def ncu (s : Bytes) : Int := s.length

/-- A byte literal. -/
def byte (n : Nat) : Byte := JInt.lit .u8 n

/-! ### Characters -/

/-- `leading_ones(u::UInt32)`. -/
def leadingOnes32 (u : Nat) : Nat :=
  ((List.range 32).find? fun k => (u / 2 ^ (31 - k)) % 2 == 0).getD 32

/-- `trailing_zeros(u::UInt32)`, 32 for zero. -/
def trailingZeros32 (u : Nat) : Nat :=
  ((List.range 32).find? fun k => (u / 2 ^ k) % 2 == 1).getD 32

/-- `ismalformed(c::Char)` on the raw `UInt32` of `c`, `base/char.jl:111-117`. -/
def ismalformed (u : Nat) : Bool :=
  let l1 := leadingOnes32 u * 8
  let t0 := Nat.land (trailingZeros32 u) 56
  l1 == 8 || l1 + t0 > 32 || (Nat.xor (Nat.land u 0x00c0c0c0) 0x00808080) / 2 ^ t0 != 0

/-- `unsafe_codepoint(c::Char)`, `base/char.jl:184-192`. -/
def unsafeCodepoint (u : Nat) : Nat :=
  if u < 0x80000000 then u / 2 ^ 24 else
    let l1 := leadingOnes32 u
    let t0 := Nat.land (trailingZeros32 u) 56
    let u := Nat.land u (0xffffffff / 2 ^ l1)
    let u := u / 2 ^ t0
    Nat.lor (Nat.lor (Nat.land u 0x7f) (Nat.land u 0x7f00 / 4))
      (Nat.lor (Nat.land u 0x7f0000 / 16) (Nat.land u 0x7f000000 / 64))

/-- Code points of Unicode categories Zs, Zl and Zp. -/
def isZsZlZp (cp : Nat) : Bool :=
  cp == 0x20 || cp == 0xa0 || cp == 0x1680 || (0x2000 ≤ cp && cp ≤ 0x200a) ||
    cp == 0x2028 || cp == 0x2029 || cp == 0x202f || cp == 0x205f || cp == 0x3000

/-- `isspace(c::Char)` on the raw `UInt32` of `c`, `base/strings/unicode.jl:624-626`:
`Char` comparisons compare raw values; `category_code` is 31 for malformed
characters (`base/strings/unicode.jl:372-382`). -/
def isspaceChar (u : Nat) : Bool :=
  u == 0x20000000 || (0x09000000 ≤ u && u ≤ 0x0d000000) || u == 0xc2850000 ||
    (0xc2a00000 ≤ u && !ismalformed u && isZsZlZp (unsafeCodepoint u))

/-- `iterate(s::String, i)`, `base/strings/string.jl:504-538`: the raw `Char`
starting at `i` and the index after it. -/
def iterate (s : Bytes) (i : Int) : Nat × Int :=
  let n := ncu s
  let b := cuN s i
  let u := b * 2 ^ 24
  if ¬ (0x80 ≤ b ∧ b ≤ 0xf7) then (u, i + 1)
  else if u < 0xc0000000 then (u, i + 1)
  else
    let i := i + 1
    if i > n then (u, i) else
    let b := cuN s i
    if Nat.land b 0xc0 != 0x80 then (u, i) else
    let u := Nat.lor u (b * 2 ^ 16)
    let i := i + 1
    if i > n ∨ u < 0xe0000000 then (u, i) else
    let b := cuN s i
    if Nat.land b 0xc0 != 0x80 then (u, i) else
    let u := Nat.lor u (b * 2 ^ 8)
    let i := i + 1
    if i > n ∨ u < 0xf0000000 then (u, i) else
    let b := cuN s i
    if Nat.land b 0xc0 != 0x80 then (u, i) else
    (Nat.lor u b, i + 1)

/-- `s[i]` for a valid in-bounds index: the same decoding as `iterate`,
`base/strings/string.jl:540-560`. -/
def getChar (s : Bytes) (i : Int) : Nat := (iterate s i).1

/-- `thisind(s, i)` for `1 ≤ i ≤ ncodeunits(s)`, `base/strings/string.jl:252-271`. -/
def thisind (s : Bytes) (i : Int) : Int :=
  let isCont (k : Int) := Nat.land (cuN s k) 0xc0 == 0x80
  if ¬ (isCont i ∧ i - 1 > 0) then i
  else if 0xc0 ≤ cuN s (i - 1) ∧ cuN s (i - 1) ≤ 0xf7 then i - 1
  else if ¬ (isCont (i - 1) ∧ i - 2 > 0) then i
  else if 0xe0 ≤ cuN s (i - 2) ∧ cuN s (i - 2) ≤ 0xf7 then i - 2
  else if ¬ (isCont (i - 2) ∧ i - 3 > 0) then i
  else if 0xf0 ≤ cuN s (i - 3) ∧ cuN s (i - 3) ≤ 0xf7 then i - 3
  else i

/-! ### Whitespace, `base/parse.jl:53-97` -/

/-- `isspace_ascii(b)`, `base/parse.jl:53`. -/
def isspaceAscii (b : Byte) : Bool := b.val == 32 || (9 ≤ b.val && b.val ≤ 13)

/-- `skipspacechar(s, i)`, `base/parse.jl:57-60`. -/
def skipspacechar (s : Bytes) (i : Int) : Int :=
  let (c, next) := iterate s i
  if isspaceChar c then next else i

/-- `skipspacechar_back(s, i, j)`, `base/parse.jl:63-66`. -/
def skipspacecharBack (s : Bytes) (i j : Int) : Int :=
  let k := thisind s j
  if k ≥ i ∧ isspaceChar (getChar s k) then k - 1 else j

/-- The loop of `skipspace(s, i, j)`, `base/parse.jl:70-82`. -/
def skipspaceLoop (s : Bytes) (j : Int) : Nat → Int → Int
  | 0, i => i
  | n+1, i =>
    if i ≤ j then
      let b := cu s i
      if isspaceAscii b then skipspaceLoop s j n (i + 1)
      else if b.val ≥ 0x80 ∧ skipspacechar s i > i then skipspaceLoop s j n (skipspacechar s i)
      else i
    else i

/-- `skipspace(s, i, j)`: the first index in `i:j` not starting a whitespace character. -/
def skipspace (s : Bytes) (i j : Int) : Int := skipspaceLoop s j (s.length + 1) i

/-- The loop of `skipspace_back(s, i, j)`, `base/parse.jl:85-97`. -/
def skipspaceBackLoop (s : Bytes) (i : Int) : Nat → Int → Int
  | 0, j => j
  | n+1, j =>
    if j ≥ i then
      let b := cu s j
      if isspaceAscii b then skipspaceBackLoop s i n (j - 1)
      else if b.val ≥ 0x80 ∧ skipspacecharBack s i j < j then
        skipspaceBackLoop s i n (skipspacecharBack s i j)
      else j
    else j

/-- `skipspace_back(s, i, j)`: the last index in `i:j` before trailing whitespace. -/
def skipspaceBack (s : Bytes) (i j : Int) : Int := skipspaceBackLoop s i (s.length + 1) j

/-- `parseint_preamble(signed, base, s, i, j)`, `base/parse.jl:102-123`:
`(sgn, base, index of the first digit)`. -/
def preamble (signed : Bool) (base : Int) (s : Bytes) (i j : Int) : Int × Int × Int :=
  let i := skipspace s i j
  if i > j then (0, 0, 0) else
  let (sgn, i, stop) :=
    if signed ∧ (cuN s i = 45 ∨ cuN s i = 43) then
      let sgn : Int := if cuN s i = 45 then -1 else 1
      let i := skipspace s (i + 1) j
      (sgn, i, decide (i > j))
    else ((1 : Int), i, false)
  if stop then (0, 0, 0) else
  if base == 0 then
    if i < j ∧ cuN s i = 48 then
      let c := cuN s (i + 1)
      let b : Int := if c = 98 then 2 else if c = 111 then 8 else if c = 120 then 16 else 10
      if b == 10 then (sgn, b, i) else (sgn, b, if i + 2 ≤ j then i + 2 else 0)
    else (sgn, 10, i)
  else (sgn, base, i)

/-! ### `Base.Parsers.parseint`, `base/parsers/ints.jl` -/

/-- `load8(buf, i)`: bytes `i:i+7` as a little-endian `UInt64`, `base/parsers/ints.jl:10-22`. -/
def load8 (buf : Bytes) (i : Int) : JInt .u64 :=
  let v : Nat := (List.range 8).foldr (fun (k : Nat) (acc : Nat) => acc * 256 + cuN buf (i + k)) 0
  JInt.wrap .u64 v

/-- `base/parsers/ints.jl:26-28`. -/
def isdigits8 (w : JInt .u64) : Bool :=
  let m := JInt.lit .u64 0xf0f0f0f0f0f0f0f0
  (bor (band w m) (shr (band (w + JInt.lit .u64 0x0606060606060606) m) 4)).val ==
    0x3333333333333333

/-- `base/parsers/ints.jl:33-38`. -/
def digits8 (w : JInt .u64) : JInt .u64 :=
  let w := w - JInt.lit .u64 0x3030303030303030
  let w := w * JInt.lit .u64 10 + shr w 8
  let m := JInt.lit .u64 0x000000ff000000ff
  shr (band w m * JInt.lit .u64 0x000f424000000064 +
    band (shr w 16) m * JInt.lit .u64 0x0000271000000001) 32

/-- `base/parsers/ints.jl:41-43`; `0x80 - lo` and `0x7f - hi` are `UInt8` differences. -/
def bytesin (w : JInt .u64) (lo hi : Byte) : JInt .u64 :=
  let ones := JInt.lit .u64 0x0101010101010101
  let a := w + JInt.rem .u64 (byte 0x80 - lo) * ones
  let b := w + JInt.rem .u64 (byte 0x7f - hi) * ones
  band (band a (bxor b (JInt.lit .u64 0xffffffffffffffff))) (JInt.lit .u64 0x8080808080808080)

/-- `base/parsers/ints.jl:46-49`. -/
def ishexdigits8 (w : JInt .u64) : Bool :=
  (band w (JInt.lit .u64 0x8080808080808080)).val == 0 &&
    (bor (bytesin w (byte 48) (byte 57))
      (bytesin (bor w (JInt.lit .u64 0x2020202020202020)) (byte 97) (byte 102))).val ==
      0x8080808080808080

/-- `base/parsers/ints.jl:54-59`. -/
def hexdigits8 (w : JInt .u64) : JInt .u64 :=
  let w := band w (JInt.lit .u64 0x0f0f0f0f0f0f0f0f) +
    band (shr w 6) (JInt.lit .u64 0x0101010101010101) * JInt.lit .u64 9
  let w := band (bor (shl w 4) (shr w 8)) (JInt.lit .u64 0x00ff00ff00ff00ff)
  let w := band (bor (shl w 8) (shr w 16)) (JInt.lit .u64 0x0000ffff0000ffff)
  band (bor (shl w 16) (shr w 32)) (JInt.lit .u64 0x00000000ffffffff)

/-- `digitvalue(b, base)`, `base/parsers/ints.jl:64-69`: `typemax(UInt8)` for a non-digit. -/
def digitvalue (b : Byte) (base : Int) : Byte :=
  if 48 ≤ b.val ∧ b.val ≤ 57 then b - byte 48
  else if 65 ≤ b.val ∧ b.val ≤ 90 then b - byte 65 + byte 10
  else if 97 ≤ b.val ∧ b.val ≤ 122 then b - byte 97 + byte (if base ≤ 36 then 10 else 36)
  else byte 255

/-- `overflowfailure(buf, i, j, base)`, `base/parsers/ints.jl:73-78`: `true` for
`OVERFLOW`, `false` for `INVALID`. -/
def overflowfailure (buf : Bytes) (i j : Int) (base : Int) : Bool :=
  (List.range (j - i + 1).toNat).all fun k => (digitvalue (cu buf (i + k)) base).val < base

/-- The number of base-`b` digits of `n > 0`. -/
def natDigits (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel+1, n => if n < b then 1 else natDigits b fuel (n / b) + 1

/-- `SAFEDIGITS64[b]` and `SAFEDIGITS128[b]`: `ndigits(typemax(U); base = b) - 1`,
`base/parsers/ints.jl:81-82`. -/
def safedigits (u : IntTy) (b : Int) : Int :=
  (natDigits b.toNat 130 (2 ^ u.bits - 1) : Int) - 1

/-- A `ParseFailure` or a value, `base/parsers/Parsers.jl:25-50`. -/
inductive PR (t : IntTy) where
  | val (v : JInt t)
  | invalid
  | overflow
  deriving DecidableEq, Repr

/-- The eight-at-a-time decimal loop, `base/parsers/ints.jl:94-99`; `none` is `INVALID`. -/
def dec8Loop {u : IntTy} (buf : Bytes) (k : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if k - i ≥ 7 then
      let w := load8 buf i
      if !isdigits8 w then none
      else dec8Loop buf k f (n * JInt.lit u 100000000 + JInt.rem u (digits8 w), i + 8)
    else some (n, i)

/-- The remaining decimal digits into a `UInt64`, `base/parsers/ints.jl:101-106`. -/
def dec1Loop {u : IntTy} (buf : Bytes) (k : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if i ≤ k then
      let d := cu buf i - byte 48
      if d.val > 9 then none
      else dec1Loop buf k f (n * JInt.lit u 10 + JInt.rem u d, i + 1)
    else some (n, i)

/-- The last decimal digits of a 128-bit value in a `UInt64` with its power of ten,
`base/parsers/ints.jl:109-116`. -/
def decTPLoop (buf : Bytes) (k : Int) :
    Nat → JInt .u64 × JInt .u64 × Int → Option (JInt .u64 × JInt .u64 × Int)
  | 0, s => some s
  | f+1, (t, p, i) =>
    if i ≤ k then
      let d := cu buf i - byte 48
      if d.val > 9 then none
      else decTPLoop buf k f (t * JInt.lit .u64 10 + JInt.rem .u64 d, p * JInt.lit .u64 10, i + 1)
    else some (t, p, i)

/-- The eight-at-a-time hexadecimal loop, `base/parsers/ints.jl:124-129`. -/
def hex8Loop {u : IntTy} (buf : Bytes) (k : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if k - i ≥ 7 then
      let w := load8 buf i
      if !ishexdigits8 w then none
      else hex8Loop buf k f (bor (shl n 32) (JInt.rem u (hexdigits8 w)), i + 8)
    else some (n, i)

/-- The remaining safe hexadecimal digits, `base/parsers/ints.jl:130-135`. -/
def hex1Loop {u : IntTy} (buf : Bytes) (k : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if i ≤ k then
      let d := digitvalue (cu buf i) 16
      if d.val ≥ 16 then none
      else hex1Loop buf k f (bor (shl n 4) (JInt.rem u d), i + 1)
    else some (n, i)

/-- The safe digits of another base, `base/parsers/ints.jl:137-143`. -/
def safeLoop {u : IntTy} (buf : Bytes) (k base : Int) : Nat → JInt u × Int → Option (JInt u × Int)
  | 0, s => some s
  | f+1, (n, i) =>
    if i ≤ k then
      let d := digitvalue (cu buf i) base
      if d.val ≥ base then none
      else safeLoop buf k base f (n * JInt.wrap u base + JInt.rem u d, i + 1)
    else some (n, i)

/-- The checked loop over the remaining digits, `base/parsers/ints.jl:146-153`:
`.inl n` when all digits fit, `.inr r` for an early `ParseFailure`. -/
def checkedLoop {u : IntTy} (t : IntTy) (buf : Bytes) (j base : Int) :
    Nat → JInt u × Int → Jl (Sum (JInt u) (PR t))
  | 0, (n, _) => pure (.inl n)
  | f+1, (n, i) =>
    if i ≤ j then
      let d := digitvalue (cu buf i) base
      if d.val ≥ base then pure (.inr .invalid)
      else do
        let (n, ovMul) ← JuliaLean.IntArith.Checked.mulWithOverflow n (JInt.wrap u base)
        let (n, ovAdd) := JuliaLean.IntArith.Checked.addWithOverflow n (JInt.rem u d)
        if ovMul || ovAdd then
          pure (.inr (if overflowfailure buf (i + 1) j base then .overflow else .invalid))
        else checkedLoop t buf j base f (n, i + 1)
    else pure (.inl n)

/-- `U` in `Parsers.parseint`: `UInt128` for 128-bit `T`, else `UInt64`
(`base/parsers/ints.jl:89`). -/
def uTy (t : IntTy) : IntTy := if t.bits > 64 then .u128 else .u64

/-- The digits of `Parsers.parseint` that cannot overflow `U`, accumulated without
checks, `base/parsers/ints.jl:90-144`: `none` is `INVALID`; otherwise the value so
far and the index of the next digit. -/
def safePrefix (t : IntTy) (buf : Bytes) (i j base : Int) : Option (JInt (uTy t) × Int) :=
  let u := uTy t
  let fuel := buf.length + 1
  if base == 10 then
    let k := min j (i + (if u == .u64 then 18 else 37))
    match dec8Loop buf k fuel (JInt.lit u 0, i) with
    | none => none
    | some (n, i) =>
      if u == .u64 then dec1Loop buf k fuel (n, i)
      else match decTPLoop buf k fuel (JInt.lit .u64 0, JInt.lit .u64 1, i) with
        | none => none
        | some (t, p, i) => some (n * JInt.rem u p + JInt.rem u t, i)
  else if t.bits < 32 then some (JInt.lit u 0, i)
  else if base == 16 then
    let k := min j (i + (if u == .u64 then 15 else 31))
    match hex8Loop buf k fuel (JInt.lit u 0, i) with
    | none => none
    | some s => hex1Loop buf k fuel s
  else
    let k := min j (i + safedigits u base - 1)
    safeLoop buf k base fuel (JInt.lit u 0, i)

/-- `Parsers.parseint(T, buf, i, j, base, neg)` for `T <: BitInteger`,
`base/parsers/ints.jl:86-157`. -/
def parseint (t : IntTy) (buf : Bytes) (i j base : Int) (neg : Bool) : Jl (PR t) :=
  if ¬ i ≤ j then pure .invalid else
  match safePrefix t buf i j base with
  | none => pure .invalid
  | some s => do
    match ← checkedLoop t buf j base (buf.length + 1) s with
    | .inr r => pure r
    | .inl n =>
      -- a negative value can reach one past `typemax(T)`
      if n.val ≤ (JInt.rem (uTy t) (JInt.typemax t) + ofBool (uTy t) neg).val then
        pure (.val (JInt.rem t (if neg then -n else n)))
      else pure .overflow

/-! ### `base/parse.jl:127-171` -/

/-- The error `throw_parseint_error(T, s, i, j, sgn, base, d)` throws,
`base/parse.jl:153-171`; it never returns. Messages are abbreviated. -/
def throwParseintError (t : IntTy) (s : Bytes) (j sgn base d : Int) : Jl JlError := do
  if sgn == 0 then return .argumentError "input string is empty or only contains whitespace"
  if ¬ (2 ≤ base ∧ base ≤ 62) then return .argumentError "invalid base"
  if d == 0 then return .argumentError "premature end of integer"
  let k := skipspaceBack s d j
  let scan : Nat → Int → Int := fun fuel p0 =>
    (List.range fuel).foldl (fun p _ =>
      if p ≤ k ∧ (digitvalue (cu s p) base).val < base then p + 1 else p) p0
  let p := scan (s.length + 1) d
  if p > d then
    if (← parseint t s d (p - 1) base (decide (sgn < 0))) == .overflow then
      return .overflowError "overflow parsing"
  if ¬ (1 ≤ p ∧ p ≤ ncu s) then return .boundsError
  let c := getChar s p
  if p > d ∧ isspaceChar c then return .argumentError "extra characters after whitespace"
  return .argumentError "invalid base digit"

/-- The arguments of the `throw_parseint_error` call when `parseint_utf8` fails. -/
structure Fail where
  sgn : Int
  base : Int
  d : Int

/-- The sign of the decimal fast path, `base/parse.jl:131`. -/
def fastNeg (t : IntTy) (s : Bytes) (i : Int) : Bool := t.signed && cuN s i == 45

/-- The first digit of the decimal fast path, after a sign, `base/parse.jl:132`. -/
def fastK (t : IntTy) (s : Bytes) (i : Int) : Int :=
  i + (if fastNeg t s i || (t.signed && cuN s i == 43) then 1 else 0)

/-- Whether `parseint_utf8` takes its decimal fast path, `base/parse.jl:129-133`:
a first digit `1-9` after an optional sign, and a last byte that is a digit
(`UInt8` differences, which wrap). -/
def fastCond (t : IntTy) (s : Bytes) (i j base : Int) : Prop :=
  (base = 0 ∨ base = 10) ∧ i ≤ j ∧ fastK t s i ≤ j ∧
    (cu s (fastK t s i) - byte 49).val ≤ 8 ∧ (cu s j - byte 48).val ≤ 9

instance (t : IntTy) (s : Bytes) (i j base : Int) : Decidable (fastCond t s i j base) := by
  unfold fastCond; infer_instance

/-- `parseint_utf8` after `parseint_preamble`, `base/parse.jl:141-146`. -/
def slowPath (t : IntTy) (s : Bytes) (j : Int) : Int × Int × Int → Jl (Sum (JInt t) Fail)
  | (sgn, b, d) =>
    if sgn ≠ 0 ∧ 2 ≤ b ∧ b ≤ 62 ∧ d ≠ 0 then
      (parseint t s d (skipspaceBack s d j) b (decide (sgn < 0))).map fun
        | .val n => .inl n
        | _ => .inr ⟨sgn, b, d⟩
    else pure (.inr ⟨sgn, b, d⟩)

/-- `parseint_utf8(T, s, i, j, base, raise)`, `base/parse.jl:127-148`, before the
`raise` branch: the value, or the arguments of the error to throw. When the fast
path fails it returns or throws directly (lines 135-138); otherwise control
continues with the preamble (line 141). -/
def parseintUtf8Core (t : IntTy) (s : Bytes) (i j base : Int) : Jl (Sum (JInt t) Fail) :=
  if fastCond t s i j base then
    (parseint t s (fastK t s i) j 10 (fastNeg t s i)).map fun
      | .val n => .inl n
      | _ => .inr ⟨if fastNeg t s i then -1 else 1, 10, fastK t s i⟩
  else slowPath t s j (preamble t.signed base s i j)

/-- `parseint_utf8(T, s, i, j, base, raise)`: `nothing` or a thrown error on failure. -/
def parseintUtf8 (t : IntTy) (s : Bytes) (i j base : Int) (raise : Bool) :
    Jl (Option (JInt t)) := do
  match ← parseintUtf8Core t s i j base with
  | .inl n => return some n
  | .inr f =>
    if raise then .error (← throwParseintError t s j f.sgn f.base f.d)
    else return none

/-- `check_valid_base(base)` and the `0` default, `base/parse.jl:234-239,259`. -/
def validBase (base : Option Int) : Jl Int :=
  match base with
  | none => pure 0
  | some b => if 2 ≤ b ∧ b ≤ 62 then pure b else .error (.argumentError "invalid base")

/-- `tryparse(T, s; base)` for `T <: BitInteger` and `s::String`, `base/parse.jl:247-262`. -/
def tryparse (t : IntTy) (s : Bytes) (base : Option Int := none) : Jl (Option (JInt t)) := do
  parseintUtf8 t s 1 (ncu s) (← validBase base) false

/-- `parse(T, s; base)` for `T <: BitInteger` and `s::String`, `base/parse.jl:250-262`. -/
def parse (t : IntTy) (s : Bytes) (base : Option Int := none) : Jl (JInt t) := do
  match ← parseintUtf8 t s 1 (ncu s) (← validBase base) true with
  | some v => pure v
  | none => .error (.argumentError "should not happen")

end JuliaLean.ParsePrint.IntParse
