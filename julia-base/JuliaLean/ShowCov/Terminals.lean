import JuliaLean.ShowCov.Basic

/-!
# `base/Terminals.jl` and `base/coreio.jl`

`TextTerminal` fallbacks dispatch to methods a concrete subtype may define.
`TextTerm` records those methods: `none` means the subtype does not override
the method, so the `TextTerminal` fallback (`error("Unimplemented")`) runs.
A `UnixTerminal` is modelled by what its methods write to `out_stream` and
`err_stream`; `write` returns the number of bytes written.
-/

namespace JuliaLean.ShowCov.Terminals

open JuliaLean.ShowCov

/-- `error("Unimplemented")`. -/
def unimplemented {α : Type} : R α := .error (.errorException "Unimplemented")

/-- The methods a concrete `TextTerminal` subtype may define. `cmove3` is
whether `cmove(t, x, y)` is defined (its result is irrelevant: the fallbacks
never reach a three-argument call). -/
structure TextTerm where
  getX : Option Int
  getY : Option Int
  displaysize : Option (Int × Int)
  cmove3 : Bool

/-- `getX(t)` with the `TextTerminal` fallback, `base/Terminals.jl:47`. -/
def getX (t : TextTerm) : R Int := match t.getX with | some x => .ok x | none => unimplemented
/-- `getY(t)` with the fallback, `base/Terminals.jl:48`. -/
def getY (t : TextTerm) : R Int := match t.getY with | some y => .ok y | none => unimplemented
/-- `displaysize(t)` with the fallback, `base/Terminals.jl:45`. -/
def displaysize (t : TextTerm) : R (Int × Int) :=
  match t.displaysize with | some d => .ok d | none => unimplemented

/-- `pipe_reader(::TextTerminal)`, `pipe_writer(::TextTerminal)`,
`displaysize(::TextTerminal)`, `cmove(t, x, y)`, `getX`, `getY`, `clear`,
`clear_line(t, row)`, `clear_line(t)`, `raw!(t, raw)` fallbacks,
`base/Terminals.jl:43-48,82-86`. -/
def textFallbackError {α : Type} : R α := unimplemented

/-- `pos(t) = (getX(t), getY(t))`, `base/Terminals.jl:49`. -/
def pos (t : TextTerm) : R (Int × Int) := do
  let x ← getX t
  let y ← getY t
  pure (x, y)

/-- `width(t) = displaysize(t)[2]`, `height(t) = displaysize(t)[1]`,
`base/Terminals.jl:76-77`. -/
def width (t : TextTerm) : R Int := do pure (← displaysize t).2
def height (t : TextTerm) : R Int := do pure (← displaysize t).1

/-- A two-argument call `cmove(x, y)`: `cmove` has only the methods
`cmove(t::TextTerminal, x, y)`, so this is a `MethodError`. -/
def cmove2 (_x _y : Int) : R Unit := .error (.methodError "cmove")

/-- `cmove_up(t::TextTerminal, n) = cmove(getX(t), max(1, getY(t)-n))`,
`base/Terminals.jl:52`. -/
def cmoveUp (t : TextTerm) (n : Int) : R Unit := do
  let x ← getX t
  let y ← getY t
  cmove2 x (max 1 (y - n))

/-- `cmove_down(t::TextTerminal, n) = cmove(getX(t), max(height(t), getY(t)+n))`,
`base/Terminals.jl:55`. -/
def cmoveDown (t : TextTerm) (n : Int) : R Unit := do
  let x ← getX t
  let h ← height t
  let y ← getY t
  cmove2 x (max h (y + n))

/-- `cmove_left(t::TextTerminal, n) = cmove(max(1, getX(t)-n), getY(t))`,
`base/Terminals.jl:58`. -/
def cmoveLeft (t : TextTerm) (n : Int) : R Unit := do
  let x ← getX t
  let y ← getY t
  cmove2 (max 1 (x - n)) y

/-- `cmove_right(t::TextTerminal, n) = cmove(max(width(t), getX(t)+n), getY(t))`,
`base/Terminals.jl:61`. -/
def cmoveRight (t : TextTerm) (n : Int) : R Unit := do
  let w ← width t
  let x ← getX t
  let y ← getY t
  cmove2 (max w (x + n)) y

/-- `cmove_line_up(t::TextTerminal, n) = cmove(1, max(1, getY(t)-n))`,
`base/Terminals.jl:64`. -/
def cmoveLineUp (t : TextTerm) (n : Int) : R Unit := do
  let y ← getY t
  cmove2 1 (max 1 (y - n))

/-- `cmove_line_down(t::TextTerminal, n) = cmove(1, max(height(t), getY(t)+n))`,
`base/Terminals.jl:67`. -/
def cmoveLineDown (t : TextTerm) (n : Int) : R Unit := do
  let h ← height t
  let y ← getY t
  cmove2 1 (max h (y + n))

/-- `cmove_col(t::TextTerminal, c) = cmove(c, getY(t))`, `base/Terminals.jl:70`. -/
def cmoveCol (t : TextTerm) (c : Int) : R Unit := do
  let y ← getY t
  cmove2 c y

/-- The one-argument forms `cmove_up(t) = cmove_up(t, 1)` etc.,
`base/Terminals.jl:53,56,59,62,65,68`. -/
def cmoveUp1 (t : TextTerm) : R Unit := cmoveUp t 1
def cmoveDown1 (t : TextTerm) : R Unit := cmoveDown t 1
def cmoveLeft1 (t : TextTerm) : R Unit := cmoveLeft t 1
def cmoveRight1 (t : TextTerm) : R Unit := cmoveRight t 1
def cmoveLineUp1 (t : TextTerm) : R Unit := cmoveLineUp t 1
def cmoveLineDown1 (t : TextTerm) : R Unit := cmoveLineDown t 1

/-- `hascolor(::TextTerminal) = false`, `flush(t::TextTerminal) = nothing`,
`beep(t::TextTerminal) = nothing`, `enable_bracketed_paste`/`disable_bracketed_paste`
fallbacks `= nothing`, `base/Terminals.jl:73,80,88,90-91`. -/
def hascolorText (_ : TextTerm) : Bool := false
def flushText (_ : TextTerm) : Unit := ()
def beepText (_ : TextTerm) : Unit := ()
def bracketedPasteText (_ : TextTerm) : Unit := ()

/-! ## `UnixTerminal` -/

/-- `CSI = "\x1b["`, `base/Terminals.jl:113`. -/
def CSI : String := "\x1b["

/-- What one `UnixTerminal` method call does: pieces written to `out_stream`,
pieces written to `err_stream`, and the returned value. -/
structure UnixCall (α : Type) where
  out : Out
  err : Out
  ret : α

/-- `write(io, s::String)` returns `sizeof(s)`. -/
def writeOut (s : String) : UnixCall Nat := ⟨[s], [], s.utf8ByteSize⟩

/-- `cmove_up/down/right/left(t::UnixTerminal, n) = write(t.out_stream, "$(CSI)$(n)X")`,
`base/Terminals.jl:115-118`; `letter` is `A`, `B`, `C` or `D`. -/
def cmoveUnix (letter : String) (n : Int) : UnixCall Nat :=
  writeOut (CSI ++ intStr n ++ letter)

def cmoveUpU (n : Int) : UnixCall Nat := cmoveUnix "A" n
def cmoveDownU (n : Int) : UnixCall Nat := cmoveUnix "B" n
def cmoveRightU (n : Int) : UnixCall Nat := cmoveUnix "C" n
def cmoveLeftU (n : Int) : UnixCall Nat := cmoveUnix "D" n

/-- `cmove_col(t::UnixTerminal, n) = (write(t.out_stream, '\r'); n > 1 && cmove_right(t, n-1))`,
`base/Terminals.jl:121`. The value is `false` when `n ≤ 1`, else the byte count
`cmove_right` returns. -/
def cmoveColU (n : Int) : UnixCall (Bool ⊕ Nat) :=
  if n > 1 then
    let r := cmoveRightU (n - 1)
    ⟨["\r"] ++ r.out, r.err, .inr r.ret⟩
  else ⟨["\r"], [], .inl false⟩

/-- `cmove_line_up(t::UnixTerminal, n) = (cmove_up(t, n); cmove_col(t, 1))` and
`cmove_line_down`, `base/Terminals.jl:119-120`. -/
def cmoveLineUpU (n : Int) : UnixCall (Bool ⊕ Nat) :=
  let a := cmoveUpU n
  let b := cmoveColU 1
  ⟨a.out ++ b.out, a.err ++ b.err, b.ret⟩
def cmoveLineDownU (n : Int) : UnixCall (Bool ⊕ Nat) :=
  let a := cmoveDownU n
  let b := cmoveColU 1
  ⟨a.out ++ b.out, a.err ++ b.err, b.ret⟩

/-- The constant escape writes, `base/Terminals.jl:149-156`. -/
def enableBracketedPasteU : UnixCall Nat := writeOut (CSI ++ "?2004h")
def disableBracketedPasteU : UnixCall Nat := writeOut (CSI ++ "?2004l")
def endKeypadTransmitModeU : UnixCall Nat := writeOut (CSI ++ "?1l\x1b>")
def clearU : UnixCall Nat := writeOut (CSI ++ "H" ++ CSI ++ "2J")
def clearLineU : UnixCall Nat := writeOut ("\r" ++ CSI ++ "0K")
/-- `beep(t::UnixTerminal) = write(t.err_stream,"\x7")`. -/
def beepU : UnixCall Nat := ⟨[], ["\x07"], 1⟩

/-- Stream-level facts a `UnixTerminal`/`TTYTerminal` method forwards to:
the `in_stream`/`out_stream` objects, the out stream's `displaysize` and its
`IOContext` properties (key ↦ value). -/
structure UnixTerm (σ : Type) where
  inStream : σ
  outStream : σ
  outDisplaysize : R (Int × Int)
  outProps : List (String × String)
  /-- `peek(t.in_stream, T)`, whose result must have type `T`. -/
  peekIn : R String
  peekIsT : Bool

/-- `pipe_reader(t::UnixTerminal) = t.in_stream::IO`, `pipe_writer = t.out_stream::IO`,
`base/Terminals.jl:97-98`. -/
def pipeReaderU {σ} (t : UnixTerm σ) : σ := t.inStream
def pipeWriterU {σ} (t : UnixTerm σ) : σ := t.outStream

/-- `Base.displaysize(t::UnixTerminal) = displaysize(t.out_stream)::Tuple{Int,Int}`,
`base/Terminals.jl:158`. -/
def displaysizeU {σ} (t : UnixTerm σ) : R (Int × Int) := t.outDisplaysize

/-- The `get(io, key, default)` lookup on the out stream: latest binding wins. -/
def propGet (props : List (String × String)) (key default : String) : String :=
  match props.find? (·.1 == key) with
  | some (_, v) => v
  | none => default

/-- `hascolor(t::TTYTerminal) = get(t.out_stream, :color, false)::Bool`,
`base/Terminals.jl:160`. A non-Bool `:color` value is a `TypeError`. -/
def hascolorTTY {σ} (t : UnixTerm σ) : R Bool :=
  match propGet t.outProps "color" "false" with
  | "true" => .ok true
  | "false" => .ok false
  | _ => .error .typeError

/-- `in`, `haskey`, `getindex`, `get` on a `TTYTerminal` forward to
`pipe_writer(t)`, `base/Terminals.jl:163-166`. -/
def inTTY {σ} (t : UnixTerm σ) (kv : String × String) : Bool :=
  propGet t.outProps kv.1 "" == kv.2 && (t.outProps.any (·.1 == kv.1))
def haskeyTTY {σ} (t : UnixTerm σ) (key : String) : Bool := t.outProps.any (·.1 == key)
def getindexTTY {σ} (t : UnixTerm σ) (key : String) : R String :=
  if haskeyTTY t key then .ok (propGet t.outProps key "") else .error (.keyError key)
def getTTY {σ} (t : UnixTerm σ) (key default : String) : String := propGet t.outProps key default

/-- `Base.peek(t::TTYTerminal, ::Type{T}) = peek(t.in_stream, T)::T`,
`base/Terminals.jl:168`. -/
def peekTTY {σ} (t : UnixTerm σ) : R String := do
  let v ← t.peekIn
  if t.peekIsT then pure v else .error .typeError

/-- `raw!(t::TTYTerminal, raw::Bool)` on Unix, `base/Terminals.jl:143-145`:
`ccall(:jl_tty_set_mode, Int32, (Ptr{Cvoid},Int32), t.in_stream.handle::Ptr{Cvoid}, raw) == 0`.
`handle` is `none` when `in_stream` has no `Ptr{Cvoid}` handle field (the field
access or the type assertion throws); `mode` is the C function's result. -/
def rawTTY (handle : Option Nat) (mode : Int) : R Bool :=
  match handle with
  | none => .error .typeError
  | some _ => .ok (mode == 0)

/-! ## `base/coreio.jl` -/

/-- Streams `print` can target. -/
inductive Stream where
  | stdout | stderr | other (n : Nat)
  deriving DecidableEq, Repr

/-- `print(io, x)` for a value whose print text is `x`: one write of `x` to `io`. -/
def printIO (io : Stream) (xs : List String) : List (Stream × String) := xs.map (io, ·)

/-- `print(x) = print(stdout, x)`, `print(x1, x2)`, `print(xs...)`,
`base/coreio.jl:6-7,11`. -/
def print0 (xs : List String) : List (Stream × String) := printIO .stdout xs
/-- `println(x) = print(stdout, x, "\n")`, `println(x1, x2)`, `println(xs...)`,
`base/coreio.jl:8-9,12`. -/
def println0 (xs : List String) : List (Stream × String) := printIO .stdout (xs ++ ["\n"])
/-- `println(io::IO) = print(io, "\n")`, `base/coreio.jl:13`. -/
def printlnIO (io : Stream) : List (Stream × String) := printIO io ["\n"]

/-- `typemax(Int)` for the `::Int` return conversion. -/
def int64Max : Nat := 2 ^ 63 - 1

/-- `write(::DevNull, ::UInt8) = 1`, `base/coreio.jl:22`. -/
def writeDevNull (_b : UInt8) : Int := 1
/-- `unsafe_write(::DevNull, ::Ptr{UInt8}, n::UInt)::Int = n`: the return
annotation converts `n` to `Int`, `base/coreio.jl:23`. -/
def unsafeWriteDevNull (n : Nat) : R Int :=
  if n ≤ int64Max then .ok n else .error (.inexactError "Int64")
/-- `bytesavailable(io::DevNull) = 0`, `base/coreio.jl:27`. -/
def bytesavailableDevNull : Int := 0

/-- Outcome of a call that may block forever. -/
inductive Wait where
  | returns
  | blocksForever
  deriving DecidableEq, Repr

/-- `closewrite(::DevNull) = nothing`, `close(::DevNull) = nothing`
(`base/coreio.jl:24-25`) return; `wait_close(::DevNull) = wait()`
(`base/coreio.jl:26`) waits on the current task with nothing to wake it. -/
def closewriteDevNull : Wait := .returns
def closeDevNull : Wait := .returns
def waitCloseDevNull : Wait := .blocksForever

/-- `write(io::CoreIO, x::UInt8) = Core.write(io, x)` and
`unsafe_write(io::CoreIO, x::Ptr{UInt8}, nb::UInt) = Core.unsafe_write(io, x, nb)`,
`base/coreio.jl:30-31`: the bytes go to the C stream. -/
def writeCore (bytes : List UInt8) : List UInt8 := bytes

/-- The read-side and status methods shared by `CoreSTDOUT`, `CoreSTDERR` and
`DevNull`, `base/coreio.jl:34-40`. -/
def readCore : R UInt8 := .error .eofError
def isopenCore : Bool := true
def isreadableCore : Bool := false
def iswritableCore : Bool := true
def flushCore : Unit := ()
def eofCore : Bool := true
def waitReadnbCore (_nb : Int) : Unit := ()

/-- `DevNull() = new()`, `base/coreio.jl:19`: the singleton, so every call is the same object. -/
def devNullCtor : Unit := ()

end JuliaLean.ShowCov.Terminals
