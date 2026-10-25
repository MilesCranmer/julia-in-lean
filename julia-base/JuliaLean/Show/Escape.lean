import JuliaLean.Show.Unicode

/-!
# String and character escaping

Models of `escape_string`, `print_quoted` and `unescape_string`
(`base/strings/io.jl`), `show(io, ::AbstractChar)` (`base/char.jl`), and the
escape decoder JuliaSyntax applies to the bodies of string and character
literals (`unescape_julia_string`, `JuliaSyntax/src/julia/literal_parsing.jl`).

A `Char` is its `UInt32` bit pattern (`Strings/Char.lean`); `Char` comparisons
such as `c <= '\\'` compare bit patterns (`base/char.jl:264`). Printers return
the bytes they write to the `IO`; the one-argument forms return the `String`
that `sprint` builds, which fails with `OutOfMemoryError` at `2^62` bytes.
`Iterators.Stateful(s)` is the list of chars `chars s` produced by `iterate`,
with `peek` the head of the remaining list.
-/

namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-- The bytes of a list of ASCII characters (used for literal byte strings). -/
def asc (cs : List Char) : List UInt8 := cs.map (fun c => c.toNat.toUInt8)

/-- The `Char` whose code point is the ASCII value `b`: bit pattern `UInt32(b) << 24`. -/
abbrev ac (b : Nat) : UInt32 := b.toUInt32 <<< 24

/-- `write(io, c::Char)`, `base/io.jl:973-980`: writes `u % UInt8` for
`u = bswap(c)` and stops once `u >>= 8` is zero. Four rounds exhaust a `UInt32`,
so the fuel never runs out. -/
def writeCharAux : Nat → UInt32 → List UInt8
  | 0, _ => []
  | k + 1, u => u.toUInt8 :: (if u >>> 8 = 0 then [] else writeCharAux k (u >>> 8))

/-- `write(io, c)` and `print(io, c)` for `c::Char` (`base/char.jl:305`). -/
def writeChar (c : UInt32) : List UInt8 := writeCharAux 4 (bswap32 c)

/-- `UInt32(c)` (`base/char.jl:158-171`) at the call sites below, all of which
have established that `c` is not malformed, where `codepoint` cannot throw
(`codepoint_ok` in `EscapeProofs.lean`). -/
def cpOf (c : UInt32) : UInt32 :=
  match codepoint c with
  | .ok u => u
  | .error _ => 0

/-- `Char(u)` for `u < 0x200000` (`base/char.jl:211-220`), which cannot throw
(`charOfU32_ok` in `EscapeProofs.lean`). -/
def charOfCp (u : Nat) : UInt32 :=
  match charOfU32 u.toUInt32 with
  | .ok c => c
  | .error _ => 0

/-- A lowercase hex digit: `d + ifelse(d > 0x9, 0x57, 0x30)`, `base/intfuncs.jl:1029-1030`;
also `hex_chars[d + 1]`, `base/char.jl:308-311`. -/
def hexDigit (d : Nat) : UInt8 := (d + if d > 9 then 0x57 else 0x30).toUInt8

/-- `(top_set_bit(x) + 3) ÷ 4`, the number of hex digits of `x` (`0` for `0`);
the fuel `16` covers every `UInt64`. -/
def nibbles : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => if x = 0 then 0 else 1 + nibbles k (x / 16)

/-- `string(x, base = 16, pad = pad)` for an unsigned `x` (`base/intfuncs.jl:1101`,
which calls `hex(x, pad, false)`, `:1020-1042`): the `max(pad, m)` low hex
digits of `x`, most significant first. -/
def hexStr (x pad : Nat) : List UInt8 :=
  (List.range (max pad (nibbles 16 x))).reverse.map (fun i => hexDigit (x / 16 ^ i % 16))

/-- `isxdigit(c::AbstractChar)`, `base/strings/unicode.jl:659`. -/
def isxdigit (c : UInt32) : Bool :=
  (decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x39)) || (decide (ac 0x61 ≤ c) && decide (c ≤ ac 0x66)) ||
    (decide (ac 0x41 ≤ c) && decide (c ≤ ac 0x46))

/-- `need_full_hex(c)`, `base/strings/io.jl:395`; `none` is `nothing`. -/
def needFullHex : Option UInt32 → Bool
  | none => false
  | some c => isxdigit c

/-- `escape_nul(c)`, `base/strings/io.jl:396-397`. -/
def escapeNul : Option UInt32 → List UInt8
  | some c => if decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x37) then asc ['\\', 'x', '0', '0']
              else asc ['\\', '0']
  | none => asc ['\\', '0']

/-- The `else` branch of `escape_string` for malformed or overlong `c`,
`base/strings/io.jl:479-484`: `"\\x"` and two hex digits for each byte
`u % UInt8` of `u = bswap(c)` until `u >>= 8` is zero. -/
def hexBytesAux : Nat → UInt32 → List UInt8
  | 0, _ => []
  | k + 1, u => asc ['\\', 'x'] ++ hexStr u.toUInt8.toNat 2 ++
      (if u >>> 8 = 0 then [] else hexBytesAux k (u >>> 8))

/-- One iteration of the loop of `escape_string(io, s, esc; keep, ascii, fullhex)`,
`base/strings/io.jl:459-486`, for the char `c` with `peek(a) = nxt`. -/
def escChar (d : UData) (esc keep : List UInt32) (ascii fullhex : Bool) (c : UInt32)
    (nxt : Option UInt32) : List UInt8 :=
  if c ∈ esc then 0x5c :: writeChar c
  else if c ∈ keep then writeChar c
  else if isasciiChar c then
    if c = ac 0 then escapeNul nxt
    else if c = ac 0x1b then asc ['\\', 'e']
    else if c = ac 0x5c then asc ['\\', '\\']
    else if decide (ac 0x07 ≤ c) && decide (c ≤ ac 0x0d) then
      [0x5c, (asc ['a', 'b', 't', 'n', 'v', 'f', 'r']).getD ((cpOf c).toNat - 7) 0]
    else if isprint d c then writeChar c
    else asc ['\\', 'x'] ++ hexStr (cpOf c).toNat 2
  else if !isoverlong c && !ismalformed c then
    if !ascii && isprint d c then writeChar c
    else if c ≤ ac 0x7f then asc ['\\', 'x'] ++ hexStr (cpOf c).toNat 2
    else if c ≤ 0xefbfbf00 then
      asc ['\\', 'u'] ++ hexStr (cpOf c).toNat (if fullhex || needFullHex nxt then 4 else 2)
    else asc ['\\', 'U'] ++ hexStr (cpOf c).toNat (if fullhex || needFullHex nxt then 8 else 4)
  else hexBytesAux 4 (bswap32 c)

/-- The loop `for c in a` of `escape_string`, `base/strings/io.jl:461`, over the
remaining chars of `a = Iterators.Stateful(s)`. -/
def escLoop (d : UData) (esc keep : List UInt32) (ascii fullhex : Bool) : List UInt32 → List UInt8
  | [] => []
  | c :: rest => escChar d esc keep ascii fullhex c rest.head? ++ escLoop d esc keep ascii fullhex rest

/-- `escape_string(io, s, esc; keep, ascii, fullhex)`, `base/strings/io.jl:459-486`:
the bytes written to `io`. -/
def escapeStringIO (d : UData) (s : JStr) (esc keep : List UInt32) (ascii fullhex : Bool) :
    List UInt8 :=
  escLoop d esc keep ascii fullhex (chars s)

/-- The `String` that `sprint` returns for the bytes `bs` written to its buffer;
Julia cannot allocate `2^62` bytes. -/
def mkStr (bs : List UInt8) : SJl JStr :=
  if h : bs.length < 2 ^ 62 then .ok ⟨bs, h⟩ else .error .outOfMemory

/-- `escape_string(s, esc = ('"',); keep = (), ascii = false, fullhex = false)`,
`base/strings/io.jl:488-489`. -/
def escapeString (d : UData) (s : JStr) (esc : List UInt32 := [ac 0x22]) (keep : List UInt32 := [])
    (ascii : Bool := false) (fullhex : Bool := false) : SJl JStr :=
  mkStr (escapeStringIO d s esc keep ascii fullhex)

/-- `print_quoted(io, s)`, `base/strings/io.jl:491-495`; also `show(io, s::String)`
(`:194`), so `repr(s)`. -/
def printQuoted (d : UData) (s : JStr) : List UInt8 :=
  [0x22] ++ escapeStringIO d s [ac 0x22, ac 0x24] [] false false ++ [0x22]

/-! ## `unescape_string` -/

/-- The digit value of `nc` in the `\x`/`\u`/`\U` loop, `base/strings/io.jl:546-548`:
`nc - '0'`, `nc - 'a' + 10`, `nc - 'A' + 10` (`Char` differences are code point
differences, `base/char.jl:296`), or `nothing` for `break`. -/
def hexVal (nc : UInt32) : Option Nat :=
  if decide (ac 0x30 ≤ nc) && decide (nc ≤ ac 0x39) then some ((cpOf nc).toNat - 0x30)
  else if decide (ac 0x61 ≤ nc) && decide (nc ≤ ac 0x66) then some ((cpOf nc).toNat - 0x61 + 10)
  else if decide (ac 0x41 ≤ nc) && decide (nc ≤ ac 0x46) then some ((cpOf nc).toNat - 0x41 + 10)
  else none

/-- `while (k += 1) <= m && !isempty(a) ... end`, `base/strings/io.jl:544-551`,
from counter `k` and value `n`; returns the final `(k, n, a)`. `n` is an `Int`
that stays below `16^8`. -/
def unescHex (m : Nat) : Nat → Nat → Nat → List UInt32 → Nat × Nat × List UInt32
  | 0, k, n, a => (k, n, a)
  | f + 1, k, n, a =>
    if k + 1 ≤ m then
      match a with
      | [] => (k + 1, n, a)
      | nc :: a' =>
        match hexVal nc with
        | some v => unescHex m f (k + 1) (n * 16 + v) a'
        | none => (k + 1, n, a)
    else (k + 1, n, a)

/-- `while (k += 1) <= 3 && !isempty(a) ... end`, `base/strings/io.jl:563-567`;
`n<<3 + c-'0'` is `Char` arithmetic whose value is `8n + codepoint(c) - 0x30`. -/
def unescOct : Nat → Nat → Nat → List UInt32 → Nat × List UInt32
  | 0, _, n, a => (n, a)
  | f + 1, k, n, a =>
    if k + 1 ≤ 3 then
      match a with
      | [] => (n, a)
      | c :: a' =>
        if decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x37) then
          unescOct f (k + 1) (n * 8 + (cpOf c).toNat - 0x30) a'
        else (n, a)
    else (n, a)

/-- The C escapes of `unescape_string`, `base/strings/io.jl:574-583`: the
character printed for `\c`, or `none` where Julia throws. -/
def unescSimple (c : UInt32) : Option UInt32 :=
  if c = ac 0x61 then some (ac 0x07)
  else if c = ac 0x62 then some (ac 0x08)
  else if c = ac 0x74 then some (ac 0x09)
  else if c = ac 0x6e then some (ac 0x0a)
  else if c = ac 0x76 then some (ac 0x0b)
  else if c = ac 0x66 then some (ac 0x0c)
  else if c = ac 0x72 then some (ac 0x0d)
  else if c = ac 0x65 then some (ac 0x1b)
  else if c = ac 0x5c || c = ac 0x22 then some c
  else none

/-- The loop of `unescape_string(io, s, keep)`, `base/strings/io.jl:535-591`, over
the remaining chars of `a`; the fuel bounds the iterations, each of which
consumes at least one char. Bytes written before an exception are discarded
with it. -/
def unescLoop (keep : List UInt32) : Nat → List UInt32 → SJl (List UInt8)
  | 0, _ => .ok []
  | _ + 1, [] => .ok []
  | f + 1, c :: a =>
    if !a.isEmpty && c = ac 0x5c then
      match a with
      | [] => .ok []
      | c :: a =>
        if c ∈ keep then (fun r => 0x5c :: writeChar c ++ r) <$> unescLoop keep f a
        else if c = ac 0x78 || c = ac 0x75 || c = ac 0x55 then
          let m := if c = ac 0x78 then 2 else if c = ac 0x75 then 4 else 8
          match unescHex m (m + 1) 0 0 a with
          | (k, n, a) =>
            if k = 1 || decide (n > 0x10ffff) then
              .error (.jl (.argumentError (if m = 2 then "invalid hex (\\x) escape sequence"
                else if m = 4 then "invalid unicode (\\u) escape sequence"
                else "invalid unicode (\\U) escape sequence")))
            else if m = 2 then (fun r => n.toUInt8 :: r) <$> unescLoop keep f a
            else (fun r => writeChar (charOfCp n) ++ r) <$> unescLoop keep f a
        else if decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x37) then
          match unescOct 3 1 ((cpOf c).toNat - 0x30) a with
          | (n, a) =>
            if n > 255 then .error (.jl (.argumentError "octal escape sequence out of range"))
            else (fun r => n.toUInt8 :: r) <$> unescLoop keep f a
        else
          match unescSimple c with
          | some e => (fun r => writeChar e ++ r) <$> unescLoop keep f a
          | none => .error (.jl (.argumentError "invalid escape sequence"))
    else (fun r => writeChar c ++ r) <$> unescLoop keep f a

/-- `unescape_string(s, keep = ())`, `base/strings/io.jl:592-593`, on the chars
`cs` of `s`. -/
def unescapeStringOf (cs : List UInt32) (keep : List UInt32) : SJl JStr :=
  match unescLoop keep (cs.length + 1) cs with
  | .ok bs => mkStr bs
  | .error e => .error e

/-- `unescape_string(s, keep = ())`, `base/strings/io.jl:592-593`. -/
def unescapeString (s : JStr) (keep : List UInt32 := []) : SJl JStr := unescapeStringOf (chars s) keep

/-! ## JuliaSyntax `unescape_julia_string` -/

/-- The hex digit loop of `unescape_julia_string`,
`JuliaSyntax/src/julia/literal_parsing.jl:258-264`: `while (k += 1) <= m && i+1 < endind`,
reading `txtbuf[i+1]`. Returns `(k, n, rest)`. -/
def jlHex (m : Nat) : Nat → Nat → Nat → List UInt8 → Nat × Nat × List UInt8
  | 0, k, n, a => (k, n, a)
  | f + 1, k, n, a =>
    if k + 1 ≤ m then
      match a with
      | [] => (k + 1, n, a)
      | nc :: a' =>
        if decide (0x30 ≤ nc) && decide (nc ≤ 0x39) then jlHex m f (k + 1) (n * 16 + (nc - 0x30).toNat) a'
        else if decide (0x61 ≤ nc) && decide (nc ≤ 0x66) then
          jlHex m f (k + 1) (n * 16 + (nc - 0x61 + 10).toNat) a'
        else if decide (0x41 ≤ nc) && decide (nc ≤ 0x46) then
          jlHex m f (k + 1) (n * 16 + (nc - 0x41 + 10).toNat) a'
        else (k + 1, n, a)
    else (k + 1, n, a)

/-- The octal digit loop, `literal_parsing.jl:280-285`. -/
def jlOct : Nat → Nat → Nat → List UInt8 → Nat × List UInt8
  | 0, _, n, a => (n, a)
  | f + 1, k, n, a =>
    if k + 1 ≤ 3 then
      match a with
      | [] => (n, a)
      | c :: a' =>
        if decide (0x30 ≤ c) && decide (c ≤ 0x37) then jlOct f (k + 1) (n * 8 + (c - 0x30).toNat) a'
        else (n, a)
    else (n, a)

/-- The C and literal escapes, `literal_parsing.jl:294-308`. -/
def jlSimple (c : UInt8) : Option UInt8 :=
  if c = 0x6e then some 0x0a
  else if c = 0x74 then some 0x09
  else if c = 0x72 then some 0x0d
  else if c = 0x65 then some 0x1b
  else if c = 0x62 then some 0x08
  else if c = 0x66 then some 0x0c
  else if c = 0x76 then some 0x0b
  else if c = 0x61 then some 0x07
  else if c = 0x5c || c = 0x27 || c = 0x22 || c = 0x24 || c = 0x60 then some c
  else none

/-- Mark the result of the rest of the loop as having seen an error. -/
def jlErr (r : List UInt8 × Bool) : List UInt8 × Bool := (r.1, true)

/-- Prepend output bytes to the result of the rest of the loop. -/
def jlOut (bs : List UInt8) (r : List UInt8 × Bool) : List UInt8 × Bool := (bs ++ r.1, r.2)

/-- The loop of `unescape_julia_string(io, txtbuf, firstind, endind, diagnostics)`,
`JuliaSyntax/src/julia/literal_parsing.jl:229-318`, over the bytes from `i` to
`endind - 1`; returns the bytes written and `had_error`. -/
def jlUnescLoop : Nat → List UInt8 → List UInt8 × Bool
  | 0, _ => ([], false)
  | _ + 1, [] => ([], false)
  | f + 1, c :: r =>
    if c ≠ 0x5c then
      if c = 0x0d then
        match r with
        | 0x0a :: r' => jlOut [0x0a] (jlUnescLoop f r')
        | _ => jlOut [0x0a] (jlUnescLoop f r)
      else jlOut [c] (jlUnescLoop f r)
    else
      match r with
      | [] => ([], true)
      | c :: r =>
        if c = 0x78 || c = 0x75 || c = 0x55 then
          let m := if c = 0x78 then 2 else if c = 0x75 then 4 else 8
          match jlHex m (m + 1) 0 0 r with
          | (k, n, r) =>
            if k = 1 || decide (n > 0x10ffff) then jlErr (jlUnescLoop f r)
            else if m = 2 then jlOut [n.toUInt8] (jlUnescLoop f r)
            else jlOut (writeChar (charOfCp n)) (jlUnescLoop f r)
        else if decide (0x30 ≤ c) && decide (c ≤ 0x37) then
          match jlOct 3 1 (c - 0x30).toNat r with
          | (n, r) =>
            if n > 255 then jlErr (jlUnescLoop f r)
            else jlOut [n.toUInt8] (jlUnescLoop f r)
        else
          match jlSimple c with
          | some u => jlOut [u] (jlUnescLoop f r)
          | none => jlErr (jlUnescLoop f r)

/-- The bytes JuliaSyntax decodes from the body of a non-raw string or char
literal, or `none` when `unescape_julia_string` reports `had_error`. -/
def juliaUnescape (body : List UInt8) : Option (List UInt8) :=
  match jlUnescLoop (body.length + 1) body with
  | (out, false) => some out
  | (_, true) => none

/-! ## `show(io, ::AbstractChar)` -/

/-- The loop of `show_invalid(io, c)`, `base/char.jl:313-323`: `\x` and the top
byte of `u` as two hex digits, then `u <<= 8`, until `u` is zero. -/
def showInvalidAux : Nat → UInt32 → List UInt8
  | 0, _ => []
  | k + 1, u => [0x5c, 0x78, hexDigit ((u >>> 28) &&& 0xf).toNat, hexDigit ((u >>> 24) &&& 0xf).toNat] ++
      (if u <<< 8 = 0 then [] else showInvalidAux k (u <<< 8))

/-- `show_invalid(io, c)`, `base/char.jl:313-323`. -/
def showInvalid (c : UInt32) : List UInt8 := [0x27] ++ showInvalidAux 4 c ++ [0x27]

/-- The escape byte `b` chosen for `c <= '\\'` in `show(io, c)`, `base/char.jl:338-348`. -/
def showEscByte (c : UInt32) : UInt8 :=
  if c = ac 0 then 0x30
  else if c = ac 0x07 then 0x61
  else if c = ac 0x08 then 0x62
  else if c = ac 0x09 then 0x74
  else if c = ac 0x0a then 0x6e
  else if c = ac 0x0b then 0x76
  else if c = ac 0x0c then 0x66
  else if c = ac 0x0d then 0x72
  else if c = ac 0x1b then 0x65
  else if c = ac 0x27 then 0x27
  else if c = ac 0x5c then 0x5c
  else 0xff

/-- `show(io, c::AbstractChar)` for `c::Char`, `base/char.jl:336-370`: the bytes of
`repr(c)`. `d = max(2, 8 - (leading_zeros(u) >> 2))` hex digits are printed,
most significant first. -/
def showChar (d : UData) (c : UInt32) : List UInt8 :=
  if c ≤ ac 0x5c ∧ showEscByte c ≠ 0xff then [0x27, 0x5c, showEscByte c, 0x27]
  else if isoverlong c || ismalformed c then showInvalid c
  else if isprint d c then [0x27] ++ writeChar c ++ [0x27]
  else
    let u := cpOf c
    let nd := max 2 (8 - clz32 u / 4)
    [0x27, 0x5c, if u ≤ 0x7f then 0x78 else if u ≤ 0xffff then 0x75 else 0x55] ++
      (List.range nd).reverse.map (fun i => hexDigit (u.toNat / 16 ^ i % 16)) ++ [0x27]

end JuliaLean.Show
