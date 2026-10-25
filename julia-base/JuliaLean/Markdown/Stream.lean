import JuliaLean.Core
import JuliaLean.Toml.Basic

/-!
# Markdown: IOBuffer reading primitives

Model of the stream helpers the Markdown parser is written in
(`stdlib/Markdown/src/parse/util.jl` at master `bbfa0ce4150`) and of the Base IO
functions they call on an `IOBuffer`.

* A Julia `String` and the contents of an `IOBuffer` are lists of bytes (`Bytes`).
  A Julia `Char` is its raw `UInt32` value (the UTF-8 bytes left-aligned), as in
  `JuliaLean.Toml`; `C 'x'` is the raw value of a character literal.
* `position(io)` is the 0-based byte offset `pos`.
* `read(io, Char)` decodes exactly as `base/io.jl:1091-1105`, so malformed UTF-8
  is represented too; `peek(io, Char)` is `read` followed by a reset
  (`base/io.jl:382-388`) and throws `EOFError` at the end of the buffer.
* Loops carry fuel; every iteration consumes at least one byte, so fuel equal to
  the input length plus one is never exhausted (`Err.outOfFuel` is a model
  artefact, never a Julia outcome).
-/

namespace JuliaLean.Markdown

/-- Bytes of a Julia `String` or of an `IOBuffer`. -/
abbrev Bytes := List Nat

/-- Raw `UInt32` value of a Julia character literal. -/
@[reducible] def C (c : Char) : Nat := Toml.ch c

/-- Exceptions thrown by the modelled functions. -/
inductive Err where
  | eofError
  | overflowError
  | argumentError
  /-- `TypeError` from a failed type assertion `x::T`. -/
  | typeError
  /-- `ErrorException` from `error(msg)`. -/
  | errorException
  /-- `MethodError` from a call with no applicable method; `fn` names the function. -/
  | methodError (fn : String)
  /-- Model artefact: fuel exhausted. -/
  | outOfFuel
  deriving Repr, DecidableEq, Inhabited

/-- An `IOBuffer` opened for reading. -/
structure Stream where
  data : Bytes
  pos : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `IOBuffer(s)`. -/
def Stream.ofBytes (s : Bytes) : Stream := ⟨s, 0⟩

abbrev M := StateT Stream (Except Err)

/-- `write(io, c::Char)`, `base/char.jl`: the bytes of the raw value from the top,
stopping once the remaining lower bytes are zero. -/
def charBytes (c : Nat) : Bytes :=
  let b3 := c / 2 ^ 24 % 256
  let b2 := c / 2 ^ 16 % 256
  let b1 := c / 2 ^ 8 % 256
  let b0 := c % 256
  b3 :: (if b2 = 0 ∧ b1 = 0 ∧ b0 = 0 then [] else
    b2 :: (if b1 = 0 ∧ b0 = 0 then [] else b1 :: (if b0 = 0 then [] else [b0])))

/-- `eof(io)`. -/
def eof : M Bool := do
  let s ← get
  return decide (s.pos ≥ s.data.length)

/-- `position(io)`. -/
def position : M Nat := do return (← get).pos

/-- `seek(io, n)`, clamped to the buffer as `base/iobuffer.jl:512-524` does. -/
def seek (n : Nat) : M Unit := modify fun s => { s with pos := min n s.data.length }

/-- `skip(io, n)`, `base/iobuffer.jl:479-494`: never before the start nor past the end. -/
def skip (n : Int) : M Unit := modify fun s =>
  { s with pos := (max 0 (min (s.pos + n) s.data.length)).toNat }

/-- `read(io, UInt8)`, `base/iobuffer.jl:436-447`. -/
def readByte : M Nat := do
  let s ← get
  match s.data[s.pos]? with
  | some b => set { s with pos := s.pos + 1 }; return b
  | none => throw .eofError

/-- `peek(io)` (a byte), `base/iobuffer.jl:450-456`. -/
def peekByte : M Nat := do
  let s ← get
  match s.data[s.pos]? with
  | some b => return b
  | none => throw .eofError

/-- `leading_ones(b)` for a byte. -/
def leadingOnes (b : Nat) : Nat :=
  if b ≥ 0xf8 then (if b ≥ 0xfc then (if b ≥ 0xfe then (if b ≥ 0xff then 8 else 7) else 6) else 5)
  else if b ≥ 0xf0 then 4 else if b ≥ 0xe0 then 3 else if b ≥ 0xc0 then 2
  else if b ≥ 0x80 then 1 else 0

/-- The continuation loop of `read(io, Char)`: shifts `s = 16, 8, 0` while `s ≥ l`. -/
def readCont (l : Nat) (c : Nat) : Nat → M Nat
  | 0 => return c
  | k + 1 => do
    let s := 8 * k
    if s ≥ l ∧ !(← eof) then
      if (← peekByte) / 64 == 2 then
        let b ← readByte
        readCont l (c + b * 2 ^ s) k
      else return c
    else return c

/-- `read(io, Char)`, `base/io.jl:1091-1105`. -/
def readChar : M Nat := do
  let b0 ← readByte
  let lo := leadingOnes b0
  let c := b0 * 2 ^ 24
  if 2 ≤ lo ∧ lo ≤ 4 then
    readCont (8 * (4 - lo)) c 3
  else return c

/-- `peek(io, Char)`, `base/io.jl:382-388`: read, then restore the position. -/
def peekChar : M Nat := do
  let p ← position
  let c ← readChar
  seek p
  return c

/-- `copyline` loop behind `readline(io; keep)`: bytes up to the next `'\n'`, which
is consumed and kept only when `keep`. -/
def readlineAux (keep : Bool) (acc : Bytes) : Nat → M Bytes
  | 0 => throw .outOfFuel
  | n + 1 => do
    if ← eof then return acc
    let b ← readByte
    if b == 10 then return (if keep then acc ++ [10] else acc)
    readlineAux keep (acc ++ [b]) n

/-- `readline(io; keep)`, `base/io.jl:714-716`. -/
def readline (keep : Bool := false) : M Bytes := do
  let s ← get
  readlineAux keep [] (s.data.length - s.pos + 1)

/-- `const whitespace = " \t\r"`, `parse/util.jl:3`. -/
def isWhitespace (c : Nat) : Bool := c == C ' ' || c == C '\t' || c == C '\r'

/-- `skipwhitespace(io; newlines)`, `parse/util.jl:9-16`. -/
def skipwhitespaceAux (newlines : Bool) : Nat → M Unit
  | 0 => throw .outOfFuel
  | n + 1 => do
    if ← eof then return
    let c ← peekChar
    if isWhitespace c || (newlines && c == C '\n') then
      let _ ← readChar
      skipwhitespaceAux newlines n
    else return

def skipwhitespace (newlines : Bool := true) : M Unit := do
  let s ← get
  skipwhitespaceAux newlines (s.data.length - s.pos + 1)

/-- String iteration (`for c in l`), `base/strings/string.jl:504-538`. -/
def decode (s : Bytes) : List Nat :=
  go 1 (s.length + 1)
where
  go (i : Int) : Nat → List Nat
    | 0 => []
    | n + 1 => match Toml.iterate s i with
      | none => []
      | some (c, j) => c :: go j n

/-- The loop of `linecontains`: `none` = `result = false; break`, otherwise the
running `result`. -/
def lineScan (chars : List Nat) (allowWs : Bool) : Bool → List Nat → Bool
  | r, [] => r
  | r, c :: cs =>
    if isWhitespace c then (if allowWs then lineScan chars allowWs r cs else false)
    else if c ∈ chars then lineScan chars allowWs true cs
    else false

/-- `linecontains(io, chars; allow_whitespace, eat, allowempty)`, `parse/util.jl:37-52`. -/
def linecontains (chars : List Nat) (allowWs : Bool := true) (eat : Bool := true)
    (allowempty : Bool := false) : M Bool := do
  let start ← position
  let l ← readline
  if l.length == 0 then return allowempty
  let result := lineScan chars allowWs allowempty (decode l)
  if !(result && eat) then seek start
  return result

/-- `blankline(io; eat)`, `parse/util.jl:54-58`. -/
def blankline (eat : Bool := true) : M Bool :=
  linecontains [] (allowWs := true) (eat := eat) (allowempty := true)

/-- `startswith(stream, c::AbstractChar; eat)`, `parse/util.jl:77-84`. -/
def startsWithChar (c : Nat) (eat : Bool := true) : M Bool := do
  if !(← eof) then
    if (← peekChar) == c then
      if eat then let _ ← readChar
      return true
  return false

/-- The character loop of `startswith(stream, s::AbstractString)`. -/
def matchChars : List Nat → M Bool
  | [] => return true
  | c :: cs => do
    if !(← eof) then
      if (← readChar) == c then return ← matchChars cs
    return false

/-- `startswith(stream, s::AbstractString; eat, padding, newlines)`, `parse/util.jl:65-75`.
`s` is given as its characters. -/
def startsWithStr (s : List Nat) (eat : Bool := true) (padding : Bool := false)
    (newlines : Bool := true) : M Bool := do
  let start ← position
  if padding then skipwhitespace newlines
  let result ← matchChars s
  if !(result && eat) then seek start
  return result

/-- `withstream(f, stream)`, `parse/util.jl:113-118`, for a block parser returning `Bool`. -/
def withstream (f : M Bool) : M Bool := do
  let pos ← position
  let result ← f
  if !result then seek pos
  return result

/-- `withstream` for an inner parser returning `nothing` or a value. -/
def withstreamOpt {α} (f : M (Option α)) : M (Option α) := do
  let pos ← position
  let result ← f
  if result.isNone then seek pos
  return result

/-- The space-counting loop of `eatindent`. -/
def countSpaces (m : Nat) : Nat → M Nat
  | 0 => throw .outOfFuel
  | n + 1 => do
    if ← startsWithChar (C ' ') then countSpaces (m + 1) n else return m

/-- `eatindent(io, n = 3)`, `parse/util.jl:123-129`. -/
def eatindent (n : Nat := 3) : M Bool := withstream do
  let s ← get
  let m ← countSpaces 0 (s.data.length - s.pos + 1)
  return decide (m ≤ n)

/-- Run a parser on the bytes `s` from the start. -/
def runOn {α} (f : M α) (s : Bytes) : Except Err (α × Stream) := f.run (Stream.ofBytes s)

end JuliaLean.Markdown
