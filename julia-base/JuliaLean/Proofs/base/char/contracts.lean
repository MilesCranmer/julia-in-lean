import JuliaLean.base.strings.unicode
import JuliaLean.base.io
import JuliaLean.Proofs.base.missing.common

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


/-- Char arithmetic moves along codepoints: for `c = Char(u)` and an `Int` `n` with
`u + n` a codepoint `Char` accepts, `c + n == Char(u + n)`. -/
def CharAddCodepoint : Prop :=
  ∀ (u c : UInt32) (n : JInt64), charOfU32 u = .ok c →
    0 ≤ (u.toNat : Int) + n.val → (u.toNat : Int) + n.val < 0x200000 →
    charAdd c n = charOfU32 (UInt32.ofNat ((u.toNat : Int) + n.val).toNat)

/-! ## `write`, `ncodeunits` -/


/-- The `ncodeunits(c::Char)` docstring, `base/char.jl:63-65`: "This is the number
of bytes which will be printed if the character is written to an output
stream". -/
def NcodeunitsWrite : Prop :=
  ∀ c : UInt32, (writeChar c).length = ncodeunitsChar c

/-! ## `show(io, c::Char)` and parsing the printed literal -/

/-- `utf8proc_category(u)` for `u ≤ 0x10ffff`: a C lookup table, left opaque. -/
opaque utf8procCategory : UInt32 → Int


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
