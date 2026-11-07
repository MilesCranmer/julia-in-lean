import JuliaLean.base.strings.util
import JuliaLean.base.iobuffer
import JuliaLean.base.char
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

def startsioEntries : List Entry := []

end JuliaLean.StringUtil
