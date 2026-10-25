import JuliaLean.Strings.Char
import JuliaLean.MissingChar.Basic

/-!
# `Char`: constructors, `codepoint`, `isvalid`, arithmetic, `show` and parsing

Builds on the `Char` encoding model of `JuliaLean/Strings/Char.lean`
(`codepoint`, `charOfU32`, `ismalformed`, `isoverlong`, `isvalidChar`,
`ncodeunitsChar`): a `Char` is its `UInt32` bit pattern. Sources are master
`bbfa0ce4150` (`base/char.jl`, `base/io.jl`, `base/strings/unicode.jl`,
`JuliaSyntax/src/julia/literal_parsing.jl`).
-/

namespace JuliaLean.MissingChar

open JuliaLean.Strings (SErr SJl codepoint charOfU32 ismalformed isoverlong isvalidChar
  ncodeunitsChar clz32 clo32 ctz32 ushr32 bswap32 land56 ix)

/-! ## `isvalid(Char, x)` for integers, `base/strings/unicode.jl:59-60` -/

/-- `isvalid(::Type{<:AbstractChar}, c::Unsigned)`, `base/strings/unicode.jl:59`. -/
def isvalidCharU (c : Nat) : Bool := decide (c ≤ 0xd7ff) || (decide (0xe000 ≤ c) && decide (c ≤ 0x10ffff))

/-- `isvalid(::Type{T}, c::Integer) = isvalid(T, Unsigned(c))`,
`base/strings/unicode.jl:60`, for `c::Int64`: `Unsigned(c)` is
`convert(UInt64, c)`, an `InexactError` for negative `c`. -/
def isvalidCharInt (c : JInt64) : Jl Bool := do
  let u ← JInt.convert .u64 c.val
  .ok (isvalidCharU u.val.toNat)

/-- `isvalid(T, value)` docstring, `base/strings/unicode.jl:34-37`: "Return `true` if
the given value is valid for that type"; for an integer it answers whether it is
a valid codepoint, without throwing. -/
def IsvalidCharInteger : Prop :=
  ∀ c : JInt64, isvalidCharInt c = .ok (decide (0 ≤ c.val) && isvalidCharU c.val.toNat)

theorem isvalidCharInteger_refuted : ¬ IsvalidCharInteger := by
  intro h
  have := h (JInt.lit .i64 (-1))
  revert this
  decide

/-! ## `codepoint` and `Char(::UInt32)` -/

/-- The codepoint docstring, `base/char.jl:83-85`: `codepoint(c)` throws "if `c`
represents a malformed character"; the `ismalformed` docstring, `:141-142`:
"Malformed data ... cannot be decoded to a codepoint (`codepoint` will throw an
exception)". -/
def CodepointThrowsMalformed : Prop :=
  ∀ c : UInt32, ismalformed c = true → ∃ e, codepoint c = .error e

theorem codepointThrowsMalformed_refuted : ¬ CodepointThrowsMalformed := by
  intro h
  obtain ⟨e, he⟩ := h 0x61620000 (by decide)
  have h2 : codepoint 0x61620000 = .ok 0x61 := by decide
  rw [h2] at he
  cases he

/-- The Char docstring, `base/char.jl:46-50`: `isvalid(c)` tells "whether `c` represents
a valid Unicode character". A valid `Char` is therefore the UTF-8 encoding of a
Unicode codepoint: `codepoint(c) ≤ 0x10ffff` and `Char(codepoint(c)) == c`. -/
def IsvalidCanonical : Prop :=
  ∀ c : UInt32, isvalidChar c = true →
    ∃ u, codepoint c = .ok u ∧ u ≤ 0x10ffff ∧ charOfU32 u = .ok c

theorem isvalidCanonical_refuted : ¬ IsvalidCanonical := by
  intro h
  obtain ⟨u, hu, hle, -⟩ := h 0xe9a9a5bf (by decide)
  have h2 : codepoint 0xe9a9a5bf = .ok 0x26997f := by decide
  rw [h2] at hu
  cases hu
  exact absurd hle (by decide)

/-- The codepoint docstring, `base/char.jl:89-92`: `codepoint(c)` "Should succeed for
any non-malformed character, i.e. when `Base.ismalformed(c)` returns `false`. This
includes invalid Unicode characters (such as unpaired surrogates) and overlong
encodings." -/
def CodepointWellFormed : Prop :=
  ∀ c : UInt32, ismalformed c = false → ∃ u, codepoint c = .ok u

/-- `Char(u::UInt32)` (`base/char.jl:211-220`) accepts exactly `u < 0x200000`
(otherwise `CodePointError`), and its result is well-formed, not overlong, and
decodes back to `u`: `codepoint(Char(u)) == u`. -/
def CharCodepointRoundTrip : Prop :=
  ∀ u : UInt32,
    (0x200000 ≤ u → charOfU32 u = .error (.codePointError u)) ∧
    (u < 0x200000 → ∃ c, charOfU32 u = .ok c ∧ codepoint c = .ok u ∧
      ismalformed c = false ∧ isoverlong c = false)

/-- The AbstractChar docstring, `base/char.jl:10-12`: "At least for valid, properly
encoded Unicode characters, these numerical codepoint values determine how
characters are compared with `<` and `==`". `isless(x::Char, y::Char)` and `==`
compare bit patterns (`base/char.jl:263-264`). Stated for every codepoint
`Char(u)` accepts. -/
def CharOrderCodepoint : Prop :=
  ∀ u v c d : UInt32, charOfU32 u = .ok c → charOfU32 v = .ok d →
    (c < d ↔ u < v) ∧ (c = d ↔ u = v)

/-- `isvalid(Char(u)) == isvalid(Char, u)`: the `isvalid(c::AbstractChar)` method
(`base/strings/unicode.jl:58`, comparing with `'\ud7ff'`, `'\ue000'`, `'\U10ffff'`)
agrees with the codepoint test of `:59` for every Char built from a codepoint. -/
def IsvalidCharCodepoint : Prop :=
  ∀ u c : UInt32, charOfU32 u = .ok c → isvalidChar c = isvalidCharU u.toNat

/-! ## Char arithmetic, `base/char.jl:276-300` -/

/-- `Int32(x::Char) = codepoint(x) % Int32`, `base/char.jl:57`. -/
def int32OfChar (c : UInt32) : SJl (JInt .i32) := do
  let u ← codepoint c
  .ok (JInt.lit .i32 u.toNat)

/-- `Char(x::Int32)`: `Char(UInt32(x))` (`base/char.jl:54`), `InexactError` for
negative `x`. -/
def charOfInt (z : Int) : SJl UInt32 :=
  if 0 ≤ z ∧ z < 2 ^ 32 then charOfU32 (UInt32.ofNat z.toNat)
  else .error (.jl (.inexactError "UInt32"))

/-- `c + y` for `c::Char`, `y::Int64`: `+(x::AbstractChar, y::Integer) = x +% y`
(`base/char.jl:299`), `+%` at `:286-295`: the ASCII fast path computes
`z = u + y` in `Int64`, otherwise `Char(Int32(x) + Int32(y))` with `Int32(y)` a
checked conversion and `+` wrapping in `Int32`. -/
def charAdd (c : UInt32) (y : JInt64) : SJl UInt32 :=
  let u : JInt .i32 := JInt.lit .i32 ((c >>> 24).toUInt8.toInt8.toInt)
  if 0 ≤ u.val then
    let z : JInt64 := JInt.lit .i64 u.val + y
    if 0 ≤ z.val ∧ z.val < 0x80 then .ok (UInt32.ofNat z.val.toNat <<< 24)
    else charOfInt z.val
  else do
    let x ← int32OfChar c
    let y32 ← match JInt.convert .i32 y.val with
      | .ok v => Except.ok v
      | .error e => Except.error (SErr.jl e)
    charOfInt (x + y32).val

/-- Char arithmetic moves along codepoints: for `c = Char(u)` and an `Int` `n` with
`u + n` a codepoint `Char` accepts, `c + n == Char(u + n)`. -/
def CharAddCodepoint : Prop :=
  ∀ (u c : UInt32) (n : JInt64), charOfU32 u = .ok c →
    0 ≤ (u.toNat : Int) + n.val → (u.toNat : Int) + n.val < 0x200000 →
    charAdd c n = charOfU32 (UInt32.ofNat ((u.toNat : Int) + n.val).toNat)

/-! ## `write`, `ncodeunits` -/

/-- `write(io, c::Char)`, `base/io.jl:973-980`: the bytes of `bswap(c)` from the
low end, stopping once the remaining bits are zero. Bound: 4 iterations. -/
def writeCharLoop : Nat → UInt32 → List UInt8
  | 0, _ => []
  | fuel + 1, u => u.toUInt8 :: (if u >>> 8 = 0 then [] else writeCharLoop fuel (u >>> 8))

def writeChar (c : UInt32) : List UInt8 := writeCharLoop 4 (bswap32 c)

/-- The `ncodeunits(c::Char)` docstring, `base/char.jl:63-65`: "This is the number
of bytes which will be printed if the character is written to an output
stream". -/
def NcodeunitsWrite : Prop :=
  ∀ c : UInt32, (writeChar c).length = ncodeunitsChar c

/-! ## `show(io, c::Char)` and parsing the printed literal -/

/-- `utf8proc_category(u)` for `u ≤ 0x10ffff`: a C lookup table, left opaque. -/
opaque utf8procCategory : UInt32 → Int

/-- `unsafe_codepoint(c::Char)`, `base/char.jl:184-192`. -/
def unsafeCodepoint (c : UInt32) : UInt32 :=
  if c < 0x80000000 then c >>> 24
  else
    let l1 := clo32 c
    let t0 := land56 (ctz32 c)
    let u := c &&& ushr32 0xffffffff l1
    let u := ushr32 u t0
    ((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
      ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6)

/-- `category_code(c::AbstractChar)` and `category_code(x::Integer)`,
`base/strings/unicode.jl:372-381`. -/
def categoryCode (c : UInt32) : Int :=
  if !ismalformed c then
    let u := unsafeCodepoint c
    if u ≤ 0x10ffff then utf8procCategory u else 30
  else 31

/-- `isprint(c) = UTF8PROC_CATEGORY_LU <= category_code(c) <= UTF8PROC_CATEGORY_ZS`,
`base/strings/unicode.jl:642` (`LU = 1`, `ZS = 23`). -/
def isprintChar (c : UInt32) : Bool := decide (1 ≤ categoryCode c) && decide (categoryCode c ≤ 23)

/-- `hex_chars[d + 1]` for a digit `d < 16`, `base/char.jl:308-311`. -/
def hexChar (d : UInt32) : UInt8 :=
  if d < 10 then (0x30 + d).toUInt8 else (0x61 + d - 10).toUInt8

/-- The loop of `show_invalid(io, c::Char)`, `base/char.jl:316-321`. Bound: 4
iterations (a `UInt32` is zero after four shifts by 8). -/
def showInvalidLoop : Nat → UInt32 → List UInt8
  | 0, _ => []
  | fuel + 1, u =>
    let a := hexChar ((u >>> 28) &&& 0xf)
    let b := hexChar ((u >>> 24) &&& 0xf)
    [0x5c, 0x78, a, b] ++ (if u <<< 8 = 0 then [] else showInvalidLoop fuel (u <<< 8))

/-- `show_invalid(io, c::Char)`, `base/char.jl:313-323`. -/
def showInvalid (c : UInt32) : List UInt8 := [0x27] ++ showInvalidLoop 4 c ++ [0x27]

/-- The hex-digit loop of `show`, `base/char.jl:363-366`: digits `d-1, ..., 0`. -/
def hexDigits (u : UInt32) : Nat → List UInt8
  | 0 => []
  | d + 1 => hexChar ((u >>> (UInt32.ofNat d <<< 2)) &&& 0xf) :: hexDigits u d

/-- `show(io::IO, c::AbstractChar)` for `c::Char`, `base/char.jl:336-370`, as the
bytes written. -/
def showChar (c : UInt32) : SJl (List UInt8) :=
  let special : UInt8 :=
    if c ≤ 0x5c000000 then
      if c = 0 then 0x30 else if c = 0x07000000 then 0x61 else if c = 0x08000000 then 0x62
      else if c = 0x09000000 then 0x74 else if c = 0x0a000000 then 0x6e
      else if c = 0x0b000000 then 0x76 else if c = 0x0c000000 then 0x66
      else if c = 0x0d000000 then 0x72 else if c = 0x1b000000 then 0x65
      else if c = 0x27000000 then 0x27 else if c = 0x5c000000 then 0x5c else 0xff
    else 0xff
  if special ≠ 0xff then .ok [0x27, 0x5c, special, 0x27]
  else if isoverlong c || ismalformed c then .ok (showInvalid c)
  else if isprintChar c then .ok ([0x27] ++ writeChar c ++ [0x27])
  else do
    let u ← codepoint c
    let tag : UInt8 := if u ≤ 0x7f then 0x78 else if u ≤ 0xffff then 0x75 else 0x55
    let d := max 2 (8 - clz32 u / 4)
    .ok ([0x27, 0x5c, tag] ++ hexDigits u d ++ [0x27])

/-- The value of an ASCII hex digit, if it is one. -/
def hexVal (b : UInt8) : Option Nat :=
  if 0x30 ≤ b ∧ b ≤ 0x39 then some (b.toNat - 0x30)
  else if 0x61 ≤ b ∧ b ≤ 0x66 then some (b.toNat - 0x61 + 10)
  else if 0x41 ≤ b ∧ b ≤ 0x46 then some (b.toNat - 0x41 + 10)
  else none

/-- The digit loop of a `\x`/`\u`/`\U` escape,
`JuliaSyntax/src/julia/literal_parsing.jl:262-268`: at most `m` hex digits.
Returns the value, the number of digits read and the rest of the text. -/
def readHex : Nat → Nat → List UInt8 → Nat × Nat × List UInt8
  | 0, n, rest => (n, 0, rest)
  | m + 1, n, b :: rest =>
    match hexVal b with
    | some v =>
      let (n', k, rest') := readHex m (n * 16 + v) rest
      (n', k + 1, rest')
    | none => (n, 0, b :: rest)
  | _ + 1, n, [] => (n, 0, [])

/-- The octal digit loop, `literal_parsing.jl:282-287`: up to two more digits. -/
def readOct : Nat → Nat → List UInt8 → Nat × List UInt8
  | 0, n, rest => (n, rest)
  | k + 1, n, b :: rest =>
    if 0x30 ≤ b ∧ b ≤ 0x37 then readOct k (n * 8 + (b.toNat - 0x30)) rest else (n, b :: rest)
  | _ + 1, n, [] => (n, [])

/-- `unescape_julia_string`, `JuliaSyntax/src/julia/literal_parsing.jl:228-320`,
on the text between the quotes. `none` means `had_error`. Bound: `fuel`, at
least the length of the text (each step consumes a byte). -/
def unescape : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => some []
  | _ + 1, [] => some []
  | fuel + 1, c :: rest =>
    if c ≠ 0x5c then
      if c = 0x0d then
        let rest := match rest with
          | 0x0a :: r => r
          | r => r
        (0x0a :: ·) <$> unescape fuel rest
      else (c :: ·) <$> unescape fuel rest
    else
      match rest with
      | [] => none
      | c :: rest =>
        if c = 0x78 ∨ c = 0x75 ∨ c = 0x55 then
          let m := if c = 0x78 then 2 else if c = 0x75 then 4 else 8
          let (n, k, rest) := readHex m 0 rest
          if k = 0 ∨ n > 0x10ffff then none
          else if m = 2 then (UInt8.ofNat n :: ·) <$> unescape fuel rest
          else
            match charOfU32 (UInt32.ofNat n) with
            | .ok ch => (writeChar ch ++ ·) <$> unescape fuel rest
            | .error _ => none
        else if 0x30 ≤ c ∧ c ≤ 0x37 then
          let (n, rest) := readOct 2 (c.toNat - 0x30) rest
          if n > 255 then none else (UInt8.ofNat n :: ·) <$> unescape fuel rest
        else
          let u : Option UInt8 :=
            if c = 0x6e then some 0x0a else if c = 0x74 then some 0x09
            else if c = 0x72 then some 0x0d else if c = 0x65 then some 0x1b
            else if c = 0x62 then some 0x08 else if c = 0x66 then some 0x0c
            else if c = 0x76 then some 0x0b else if c = 0x61 then some 0x07
            else if c = 0x5c then some 0x5c else if c = 0x27 then some 0x27
            else if c = 0x22 then some 0x22 else if c = 0x24 then some 0x24
            else if c = 0x60 then some 0x60 else none
          match u with
          | none => none
          | some b => (b :: ·) <$> unescape fuel rest

/-- The continuation loop of `read(io::IO, ::Type{Char})`, `base/io.jl:1097-1103`.
Bound: at most 3 continuation bytes. -/
def readCharCont : Nat → UInt32 → Nat → Nat → List UInt8 → UInt32 × List UInt8
  | 0, c, _, _, rest => (c, rest)
  | fuel + 1, c, s, l, rest =>
    if s ≥ l then
      match rest with
      | b :: rest' =>
        if b &&& 0xc0 = 0x80 then readCharCont fuel (c ||| (b.toUInt32 <<< UInt32.ofNat s)) (s - 8) l rest'
        else (c, rest)
      | [] => (c, rest)
    else (c, rest)

/-- `read(io::IO, ::Type{Char})`, `base/io.jl:1091-1105`, on a nonempty byte list:
the Char and the unread bytes. -/
def readChar : List UInt8 → Option (UInt32 × List UInt8)
  | [] => none
  | b0 :: rest =>
    let lo := clo32 (b0.toUInt32 <<< 24)
    let c := b0.toUInt32 <<< 24
    if 2 ≤ lo ∧ lo ≤ 4 then some (readCharCont 3 c 16 (8 * (4 - lo)) rest)
    else some (c, rest)

/-- Parsing a character literal `'...'` (`JuliaSyntax/src/julia/literal_parsing.jl:386-396`):
unescape the text between the quotes, read one `Char`, and require that nothing
is left. `none` is a parse error. The printed literals contain no unescaped `'`,
so the tokenizer's literal is the whole text. -/
def parseCharLit (bs : List UInt8) : Option UInt32 :=
  match bs with
  | 0x27 :: body =>
    if body.getLast? ≠ some 0x27 then none
    else
      match unescape (body.length) body.dropLast with
      | none => none
      | some txt =>
        match readChar txt with
        | some (c, []) => some c
        | _ => none
  | _ => none

/-- The `show` docstring (`base/show.jl`): the printed form "should be parseable Julia
code when possible". Every well-formed, non-overlong `Char` has a literal (its
UTF-8 bytes as `\x` escapes), so `repr(c)` should parse back to `c`. -/
def ShowCharParses : Prop :=
  ∀ c : UInt32, ismalformed c = false → isoverlong c = false →
    ∀ bs, showChar c = .ok bs → parseCharLit bs = some c

theorem showCharParses_refuted : ¬ ShowCharParses := by
  intro h
  have := h 0xf4908080 (by decide) (by decide)
    [0x27, 0x5c, 0x55, 0x31, 0x31, 0x30, 0x30, 0x30, 0x30, 0x27] (by decide)
  revert this
  decide

end JuliaLean.MissingChar
