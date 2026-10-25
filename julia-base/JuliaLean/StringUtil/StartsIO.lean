import JuliaLean.IOBuffers.Model
import JuliaLean.Strings.Char
import JuliaLean.Registry.Types

/-!
# `startswith(io::IO, prefix)`

`base/strings/util.jl:87-105` (master `bbfa0ce4150`) on an `IOBuffer`, with the
`IOBuffer` model of the IOBuffers area (`JuliaLean/IOBuffers/Model.lean`) and the
generic `read(io::IO, ::Type{Char})` of `base/io.jl:1091-1106`.

A `Char` is its 32-bit bit pattern, as in `JuliaLean/Strings`.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.IOBuffers

/-- The continuation-byte loop of `read(io::IO, ::Type{Char})`, `base/io.jl:1097-1103`:
`while s ≥ l && !eof(io); peek(io) & 0xc0 == 0x80 || break; b = read(io, UInt8);
c |= UInt32(b) << s; s -= 8; end`. `s` starts at 16 and drops by 8 per step while
`l ≥ 0`, so three steps exhaust the loop; the first argument is that bound. -/
def readCharLoop (l : Int) : Nat → Int → UInt32 → M UInt32
  | 0, _, c => pure c
  | k + 1, s, c => do
    let io ← get
    if !(decide (s ≥ l) && !eof io) then return c
    let p ← peekByte
    if (p &&& 0xc0) != 0x80 then return c
    let b ← readByte
    readCharLoop l k (s - 8) (c ||| (b.toUInt32 <<< UInt32.ofNat s.toNat))

/-- `read(io::IO, ::Type{Char})`, `base/io.jl:1091-1106`. `leading_ones(b0)` is
`Strings.clo32` of the byte in the top position; `l = 0x08 * (0x04 - lo)`. -/
def readChar : M UInt32 := do
  let b0 ← readByte
  let lo := Strings.clo32 (b0.toUInt32 <<< 24)
  let c : UInt32 := b0.toUInt32 <<< 24
  if 2 ≤ lo ∧ lo ≤ 4 then readCharLoop (8 * (4 - (lo : Int))) 3 16 c else pure c

/-- `startswith(io::IO, prefix::Base.Chars)`, `base/strings/util.jl:93-98`, for a
tuple or vector of characters `cs`: `mark(io); c = read(io, Char); reset(io); c in prefix`. -/
def startswithChars (cs : List UInt32) : M Bool := do
  discard mark
  let c ← readChar
  discard reset
  return cs.contains c

/-- `startswith(io::IO, prefix::UTF8String)`, `base/strings/util.jl:99-104`:
`mark(io); s = read(io, ncodeunits(prefix)); reset(io); s == codeunits(prefix)`. -/
def startswithStr (p : List UInt8) : M Bool := do
  discard mark
  let s ← readN (i p.length)
  discard reset
  return s == p

/-- `n` calls of `read(io, UInt8)`. -/
def readBytes : Nat → M Unit
  | 0 => pure ()
  | n + 1 => do discard readByte; readBytes n

/-- `io = IOBuffer(data)` followed by `k` byte reads. -/
def openRead (data : List UInt8) (k : Nat) : Except IOErr IOBuf :=
  match iobufferString data with
  | .error e => .error e
  | .ok io =>
    match (readBytes k).run io with
    | .ok _ io' => .ok io'
    | .error e _ => .error e

/-- `openRead data k` followed by `mark(io)`. -/
def markedAfter (data : List UInt8) (k : Nat) : Except IOErr IOBuf :=
  match openRead data k with
  | .error e => .error e
  | .ok io =>
    match (mark).run io with
    | .ok _ io' => .ok io'
    | .error e _ => .error e

/-- The value returned by a method, or `none` if it throws. -/
def result {α} (m : M α) (io : IOBuf) : Option α :=
  match m.run io with
  | .ok a _ => some a
  | .error _ _ => none

/-- Whether a method that returns leaves the stream's mark where it was. -/
def keepsMark {α} (m : M α) (io : IOBuf) : Bool :=
  match m.run io with
  | .ok _ io' => io'.mark == io.mark
  | .error _ _ => true

/-! ## Properties -/

/-- `startswith(io, prefix)` only checks the stream (its docstring points to `peek`): on a
marked `IOBuffer`, every call that returns leaves the caller's mark in place. -/
def keepsMarkAfter (data p : List UInt8) (cs : List UInt32) (k : Nat) : Bool :=
  match markedAfter data k with
  | .ok io => keepsMark (startswithStr p) io && keepsMark (startswithChars cs) io
  | .error _ => true

def StartswithIoKeepsMark : Prop :=
  ∀ (data p : List UInt8) (cs : List UInt32) (k : Nat), keepsMarkAfter data p cs k = true

/-- `IOBuffer("abc")`. -/
def dataAbc : List UInt8 := [0x61, 0x62, 0x63]

theorem startswithIoKeepsMark_refuted : ¬ StartswithIoKeepsMark := by
  intro h
  have := h dataAbc [0x62] [0x62000000] 1
  revert this; decide

/-- `startswith(io, chars)` on a stream at its end returns `false`, as
`startswith(io, prefix::String)` and `startswith("", chars)` do. -/
def falseAtEnd (data : List UInt8) (cs : List UInt32) : Bool :=
  match openRead data data.length with
  | .ok io => result (startswithChars cs) io == some false
  | .error _ => true

def StartswithIoEof : Prop :=
  ∀ (data : List UInt8) (cs : List UInt32), falseAtEnd data cs = true

theorem startswithIoEof_refuted : ¬ StartswithIoEof := by
  intro h
  have := h [] [0x61000000]
  revert this; decide

/-! ## Registry -/

open JuliaLean.Registry

def startsioEntries : List Entry := [
  { id := "stringutil-startswith-io-mark"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::IO, ::AbstractString)", "startswith(::IO, ::Base.Chars)"]
    statement := "On a marked IOBuffer (IOBuffer(data), k bytes read, mark(io)), startswith(io, prefix) for a string or a collection of characters, whenever it returns, leaves the caller's mark in place."
    source := "base/strings/util.jl:87-92 (startswith(io::IO, prefix) docstring: \"Check if an `IO` object starts with a prefix ... See also `peek`\")"
    status := .refuted
    prop := ``StartswithIoKeepsMark
    thm := some ``startswithIoKeepsMark_refuted
    issue := "none found; related #40616 (queries: issues: startswith IO, prs: startswith IO, issues: startswith IOBuffer, issues: startswith mark reset)"
    notes := "IOBuffer(\"abc\") after reading 'a' and mark(io): startswith(io, \"b\") and startswith(io, ['b']) return true but unmark the stream (mark/read/reset, base/strings/util.jl:93-104); a later reset(io) throws. Same pattern as peek (bugs/iobuffers-peek-clears-mark.yaml). Model checked against Julia nightly on 12 inputs." },
  { id := "stringutil-startswith-io-eof"
    juliaFile := "base/strings/util.jl"
    juliaFns := ["startswith(::IO, ::Base.Chars)", "read(::IO, ::Type{Char})"]
    statement := "startswith(io, chars) on an IOBuffer at its end returns false, as startswith(io, prefix::String) and startswith(\"\", chars) do."
    source := "base/strings/util.jl:87-92 (startswith(io::IO, prefix) docstring)"
    status := .refuted
    prop := ``StartswithIoEof
    thm := some ``startswithIoEof_refuted
    issue := "none found; related #40616 (queries: issues: startswith IO, issues: startswith IOBuffer, issues: startswith EOFError, prs: startswith EOFError)"
    notes := "startswith(IOBuffer(\"\"), 'a') throws EOFError from read(io, Char) (base/io.jl:1092) after mark(io), so the buffer also stays marked." }
]

end JuliaLean.StringUtil
