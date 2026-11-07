import JuliaLean.base.io
import JuliaLean.base.coreio

/-!
# Model of `base/Terminals.jl`

Typed model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Each method carries its verbatim source and follows its body. Streams and mutable
worlds use `base.io.M`; typed callees select user-extensible IO and numeric methods.
The two-argument `cmove` calls in the TextTerminal fallbacks are preserved exactly,
including their missing terminal argument. Missing fields of TerminalBuffer raise
Julia field errors through the field-access interface. Platform branches are explicit.
-/

namespace JuliaLean.base.Terminals
open JuliaLean
open JuliaLean.base.io (M Error)

abbrev I := JInt64
def i (z : Int) : I := JInt.wrap .i64 z

structure TextOps (World Terminal Number Result : Type) where
  getX : Terminal → M World Number
  getY : Terminal → M World Number
  displaysize : Terminal → M World (I × I)
  height : Terminal → M World Number
  width : Terminal → M World Number
  cmove2 : Number → Number → M World Result
  one : Number
  add : Number → Number → Number
  sub : Number → Number → Number
  max : Number → Number → Number

structure UnixFields (World Terminal Stream : Type) where
  inStream : Terminal → M World Stream
  outStream : Terminal → M World Stream
  errStream : Terminal → M World Stream

structure StreamOps (World Stream Number : Type) where
  write : Stream → String → M World I
  numberString : Number → M World String
  one : Number
  greaterOne : Number → Bool
  subOne : Number → Number
  displaysize : Stream → M World (I × I)

structure RawOps (World Stream Handle : Type) where
  ispty : Stream → M World Bool
  runStty : Bool → Stream → Stream → Stream → M World Unit
  handle : Stream → M World Handle
  ttySetMode : Handle → Bool → M World (JInt .i32)
  isProcessFailed : Error → Bool

/--
Julia source: base/Terminals.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type AbstractTerminal <: Base.AbstractPipe end
```
-/
abbrev AbstractTerminal (Terminal : Type) := Terminal

/--
Julia source: base/Terminals.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type TextTerminal <: AbstractTerminal end
```
-/
abbrev TextTerminal (Terminal : Type) := Terminal

/--
Julia source: base/Terminals.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_reader(::TextTerminal) = error("Unimplemented")
```
-/
def pipeReaderText {World Terminal Stream : Type} (_t : Terminal) : M World Stream :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_writer(::TextTerminal) = error("Unimplemented")
```
-/
def pipeWriterText {World Terminal Stream : Type} (_t : Terminal) : M World Stream :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
displaysize(::TextTerminal) = error("Unimplemented")
```
-/
def displaysizeText {World Terminal : Type} (_t : Terminal) : M World (I × I) :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove(t::TextTerminal, x, y) = error("Unimplemented")
```
-/
def cmoveText {World Terminal X Y Result : Type} (_t : Terminal) (_x : X) (_y : Y) : M World Result :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getX(t::TextTerminal) = error("Unimplemented")
```
-/
def getXText {World Terminal Number : Type} (_t : Terminal) : M World Number :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getY(t::TextTerminal) = error("Unimplemented")
```
-/
def getYText {World Terminal Number : Type} (_t : Terminal) : M World Number :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:82-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
clear(t::TextTerminal) = error("Unimplemented")
```
-/
def clearText {World Terminal : Type} (_t : Terminal) : M World Unit :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
clear_line(t::TextTerminal, row) = error("Unimplemented")
```
-/
def clearLineRowText {World Terminal Number : Type} (_t : Terminal) (_row : Number) : M World Unit :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
clear_line(t::TextTerminal) = error("Unimplemented")
```
-/
def clearLineText {World Terminal : Type} (_t : Terminal) : M World Unit :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
raw!(t::TextTerminal, raw::Bool) = error("Unimplemented")
```
-/
def rawText {World Terminal : Type} (_t : Terminal) (_raw : Bool) : M World Bool :=
  throw (.errorException "Unimplemented")

/--
Julia source: base/Terminals.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pos(t::TextTerminal) = (getX(t), getY(t))
```
-/
def pos {World Terminal Number Result : Type} (ops : TextOps World Terminal Number Result)
    (t : Terminal) : M World (Number × Number) := do
  let x ← ops.getX t
  let y ← ops.getY t
  pure (x, y)

/--
Julia source: base/Terminals.jl:52-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_up(t::TextTerminal, n) = cmove(getX(t), max(1, getY(t)-n))
```
-/
def cmoveUpText {World Terminal Number Result : Type} (ops : TextOps World Terminal Number Result)
    (t : Terminal) (n : Number) : M World Result := do
  ops.cmove2 (← ops.getX t) (ops.max ops.one (ops.sub (← ops.getY t) n))

/--
Julia source: base/Terminals.jl:55-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_down(t::TextTerminal, n) = cmove(getX(t), max(height(t), getY(t)+n))
```
-/
def cmoveDownText {World Terminal Number Result : Type} (ops : TextOps World Terminal Number Result)
    (t : Terminal) (n : Number) : M World Result := do
  ops.cmove2 (← ops.getX t) (ops.max (← ops.height t) (ops.add (← ops.getY t) n))

/--
Julia source: base/Terminals.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_left(t::TextTerminal, n) = cmove(max(1, getX(t)-n), getY(t))
```
-/
def cmoveLeftText {World Terminal Number Result : Type} (ops : TextOps World Terminal Number Result)
    (t : Terminal) (n : Number) : M World Result := do
  ops.cmove2 (ops.max ops.one (ops.sub (← ops.getX t) n)) (← ops.getY t)

/--
Julia source: base/Terminals.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_right(t::TextTerminal, n) = cmove(max(width(t), getX(t)+n), getY(t))
```
-/
def cmoveRightText {World Terminal Number Result : Type} (ops : TextOps World Terminal Number Result)
    (t : Terminal) (n : Number) : M World Result := do
  ops.cmove2 (ops.max (← ops.width t) (ops.add (← ops.getX t) n)) (← ops.getY t)

/--
Julia source: base/Terminals.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_line_up(t::TextTerminal, n) = cmove(1, max(1, getY(t)-n))
```
-/
def cmoveLineUpText {World Terminal Number Result : Type} (ops : TextOps World Terminal Number Result)
    (t : Terminal) (n : Number) : M World Result := do
  ops.cmove2 ops.one (ops.max ops.one (ops.sub (← ops.getY t) n))

/--
Julia source: base/Terminals.jl:67-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_line_down(t::TextTerminal, n) = cmove(1, max(height(t), getY(t)+n))
```
-/
def cmoveLineDownText {World Terminal Number Result : Type} (ops : TextOps World Terminal Number Result)
    (t : Terminal) (n : Number) : M World Result := do
  ops.cmove2 ops.one (ops.max (← ops.height t) (ops.add (← ops.getY t) n))

/--
Julia source: base/Terminals.jl:70-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_col(t::TextTerminal, c) = cmove(c, getY(t))
```
-/
def cmoveColText {World Terminal Number Result : Type} (ops : TextOps World Terminal Number Result)
    (t : Terminal) (n : Number) : M World Result := do
  ops.cmove2 n (← ops.getY t)

/--
Julia source: base/Terminals.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_up(t) = cmove_up(t, 1)
```
-/
def cmoveUpDefault {m : Type → Type} {Terminal Number Result : Type}
    (move : Terminal → Number → m Result) (one : Number) (t : Terminal) : m Result := move t one

/--
Julia source: base/Terminals.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_down(t) = cmove_down(t, 1)
```
-/
def cmoveDownDefault {m : Type → Type} {Terminal Number Result : Type}
    (move : Terminal → Number → m Result) (one : Number) (t : Terminal) : m Result := move t one

/--
Julia source: base/Terminals.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_left(t) = cmove_left(t, 1)
```
-/
def cmoveLeftDefault {m : Type → Type} {Terminal Number Result : Type}
    (move : Terminal → Number → m Result) (one : Number) (t : Terminal) : m Result := move t one

/--
Julia source: base/Terminals.jl:62-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_right(t) = cmove_right(t, 1)
```
-/
def cmoveRightDefault {m : Type → Type} {Terminal Number Result : Type}
    (move : Terminal → Number → m Result) (one : Number) (t : Terminal) : m Result := move t one

/--
Julia source: base/Terminals.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_line_up(t) = cmove_line_up(t, 1)
```
-/
def cmoveLineUpDefault {m : Type → Type} {Terminal Number Result : Type}
    (move : Terminal → Number → m Result) (one : Number) (t : Terminal) : m Result := move t one

/--
Julia source: base/Terminals.jl:68-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_line_down(t) = cmove_line_down(t, 1)
```
-/
def cmoveLineDownDefault {m : Type → Type} {Terminal Number Result : Type}
    (move : Terminal → Number → m Result) (one : Number) (t : Terminal) : m Result := move t one

/--
Julia source: base/Terminals.jl:73-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hascolor(::TextTerminal) = false
```
-/
def hascolorText {Terminal : Type} (_t : Terminal) : Bool := false

/--
Julia source: base/Terminals.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
width(t::TextTerminal) = (displaysize(t)::Tuple{Int,Int})[2]
```
-/
def width {World Terminal : Type} (displaysize : Terminal → M World (I × I))
    (t : Terminal) : M World I := do pure (← displaysize t).2

/--
Julia source: base/Terminals.jl:77-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
height(t::TextTerminal) = (displaysize(t)::Tuple{Int,Int})[1]
```
-/
def height {World Terminal : Type} (displaysize : Terminal → M World (I × I))
    (t : Terminal) : M World I := do pure (← displaysize t).1

/--
Julia source: base/Terminals.jl:80-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flush(t::TextTerminal) = nothing
```
-/
def flushText {World Terminal : Type} (_t : Terminal) : M World Unit := pure ()

/--
Julia source: base/Terminals.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
beep(t::TextTerminal) = nothing
```
-/
def beepText {World Terminal : Type} (_t : Terminal) : M World Unit := pure ()

/--
Julia source: base/Terminals.jl:90-90 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
enable_bracketed_paste(t::TextTerminal) = nothing
```
-/
def enableBracketedPasteText {World Terminal : Type} (_t : Terminal) : M World Unit := pure ()

/--
Julia source: base/Terminals.jl:91-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
disable_bracketed_paste(t::TextTerminal) = nothing
```
-/
def disableBracketedPasteText {World Terminal : Type} (_t : Terminal) : M World Unit := pure ()

/--
Julia source: base/Terminals.jl:95-95 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type UnixTerminal <: TextTerminal end
```
-/
abbrev UnixTerminal (Terminal : Type) := Terminal

/--
Julia source: base/Terminals.jl:97-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_reader(t::UnixTerminal) = t.in_stream::IO
```
-/
def pipeReaderUnix {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (t : Terminal) : M World Stream := fields.inStream t

/--
Julia source: base/Terminals.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_writer(t::UnixTerminal) = t.out_stream::IO
```
-/
def pipeWriterUnix {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (t : Terminal) : M World Stream := fields.outStream t

/--
Julia source: base/Terminals.jl:101-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct TerminalBuffer <: UnixTerminal
    out_stream::IO
end
```
-/
structure TerminalBuffer (Stream : Type) where
  out_stream : Stream

/--
Julia source: base/Terminals.jl:105-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct TTYTerminal <: UnixTerminal
    term_type::String
    in_stream::IO
    out_stream::IO
    err_stream::IO
end
```
-/
structure TTYTerminal (Stream : Type) where
  term_type : String
  in_stream : Stream
  out_stream : Stream
  err_stream : Stream

def ttyFields {World Stream : Type} : UnixFields World (TTYTerminal Stream) Stream where
  inStream t := pure t.in_stream
  outStream t := pure t.out_stream
  errStream t := pure t.err_stream

def bufferFields {World Stream : Type} : UnixFields World (TerminalBuffer Stream) Stream where
  inStream _ := throw (.errorException "type TerminalBuffer has no field in_stream")
  outStream t := pure t.out_stream
  errStream _ := throw (.errorException "type TerminalBuffer has no field err_stream")

/--
Julia source: base/Terminals.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const CSI = "\x1b["
```
-/
def CSI : String := "\x1b["

/--
Julia source: base/Terminals.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_up(t::UnixTerminal, n) = write(t.out_stream, "$(CSI)$(n)A")
```
-/
def cmoveUpUnix {World Terminal Stream Number : Type} (fields : UnixFields World Terminal Stream)
    (ops : StreamOps World Stream Number) (t : Terminal) (n : Number) : M World I := do
  let stream ← fields.outStream t
  let count ← ops.numberString n
  ops.write stream (CSI ++ count ++ "A")

/--
Julia source: base/Terminals.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_down(t::UnixTerminal, n) = write(t.out_stream, "$(CSI)$(n)B")
```
-/
def cmoveDownUnix {World Terminal Stream Number : Type} (fields : UnixFields World Terminal Stream)
    (ops : StreamOps World Stream Number) (t : Terminal) (n : Number) : M World I := do
  let stream ← fields.outStream t
  let count ← ops.numberString n
  ops.write stream (CSI ++ count ++ "B")

/--
Julia source: base/Terminals.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_right(t::UnixTerminal, n) = write(t.out_stream, "$(CSI)$(n)C")
```
-/
def cmoveRightUnix {World Terminal Stream Number : Type} (fields : UnixFields World Terminal Stream)
    (ops : StreamOps World Stream Number) (t : Terminal) (n : Number) : M World I := do
  let stream ← fields.outStream t
  let count ← ops.numberString n
  ops.write stream (CSI ++ count ++ "C")

/--
Julia source: base/Terminals.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_left(t::UnixTerminal, n) = write(t.out_stream, "$(CSI)$(n)D")
```
-/
def cmoveLeftUnix {World Terminal Stream Number : Type} (fields : UnixFields World Terminal Stream)
    (ops : StreamOps World Stream Number) (t : Terminal) (n : Number) : M World I := do
  let stream ← fields.outStream t
  let count ← ops.numberString n
  ops.write stream (CSI ++ count ++ "D")

/--
Julia source: base/Terminals.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_col(t::UnixTerminal, n) = (write(t.out_stream, '\r'); n > 1 && cmove_right(t, n-1))
```
-/
def cmoveColUnix {World Terminal Stream Number : Type} (fields : UnixFields World Terminal Stream)
    (ops : StreamOps World Stream Number) (t : Terminal) (n : Number) : M World (Sum Bool I) := do
  let _ ← ops.write (← fields.outStream t) "\r"
  if ops.greaterOne n then return .inr (← cmoveRightUnix fields ops t (ops.subOne n))
  pure (.inl false)

/--
Julia source: base/Terminals.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_line_up(t::UnixTerminal, n) = (cmove_up(t, n); cmove_col(t, 1))
```
-/
def cmoveLineUpUnix {World Terminal Stream Number : Type} (fields : UnixFields World Terminal Stream)
    (ops : StreamOps World Stream Number) (t : Terminal) (n : Number) : M World (Sum Bool I) := do
  let _ ← cmoveUpUnix fields ops t n
  cmoveColUnix fields ops t ops.one

/--
Julia source: base/Terminals.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cmove_line_down(t::UnixTerminal, n) = (cmove_down(t, n); cmove_col(t, 1))
```
-/
def cmoveLineDownUnix {World Terminal Stream Number : Type} (fields : UnixFields World Terminal Stream)
    (ops : StreamOps World Stream Number) (t : Terminal) (n : Number) : M World (Sum Bool I) := do
  let _ ← cmoveDownUnix fields ops t n
  cmoveColUnix fields ops t ops.one

/--
Julia source: base/Terminals.jl:124-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function raw!(t::TTYTerminal,raw::Bool)
        if Base.ispty(t.in_stream)
            try
                run((raw ? `stty raw -echo onlcr -ocrnl opost` : `stty sane`),
                    t.in_stream, t.out_stream, t.err_stream)
                true
            catch ex
                # Fall back to ccall if stty fails (e.g., in some CI environments)
                if ex isa ProcessFailedException
                    ccall(:jl_tty_set_mode, Int32, (Ptr{Cvoid},Int32), t.in_stream.handle::Ptr{Cvoid}, raw) == 0
                else
                    rethrow()
                end
            end
        else
            ccall(:jl_tty_set_mode, Int32, (Ptr{Cvoid},Int32), t.in_stream.handle::Ptr{Cvoid}, raw) == 0
        end
    end
```
-/
def rawWindows {World Stream Handle : Type} (ops : RawOps World Stream Handle)
    (t : TTYTerminal Stream) (raw : Bool) : M World Bool := do
  if ← ops.ispty t.in_stream then
    try
      ops.runStty raw t.in_stream t.out_stream t.err_stream
      pure true
    catch error =>
      if ops.isProcessFailed error then
        return (← ops.ttySetMode (← ops.handle t.in_stream) raw).val == 0
      else throw error
  else
    return (← ops.ttySetMode (← ops.handle t.in_stream) raw).val == 0

/--
Julia source: base/Terminals.jl:143-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function raw!(t::TTYTerminal, raw::Bool)
        ccall(:jl_tty_set_mode, Int32, (Ptr{Cvoid},Int32), t.in_stream.handle::Ptr{Cvoid}, raw) == 0
    end
```
-/
def rawUnix {World Stream Handle : Type} (ops : RawOps World Stream Handle)
    (t : TTYTerminal Stream) (raw : Bool) : M World Bool := do
  return (← ops.ttySetMode (← ops.handle t.in_stream) raw).val == 0

/--
Julia source: base/Terminals.jl:149-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval enable_bracketed_paste(t::UnixTerminal) = write(t.out_stream, $"$(CSI)?2004h")
```
-/
def enableBracketedPasteUnix {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (write : Stream → String → M World I) (t : Terminal) : M World I := do
  write (← fields.outStream t) "\x1b[?2004h"

/--
Julia source: base/Terminals.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval disable_bracketed_paste(t::UnixTerminal) = write(t.out_stream, $"$(CSI)?2004l")
```
-/
def disableBracketedPasteUnix {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (write : Stream → String → M World I) (t : Terminal) : M World I := do
  write (← fields.outStream t) "\x1b[?2004l"

/--
Julia source: base/Terminals.jl:151-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval end_keypad_transmit_mode(t::UnixTerminal) = # tput rmkx
    write(t.out_stream, $"$(CSI)?1l\x1b>")
```
-/
def endKeypadTransmitMode {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (write : Stream → String → M World I) (t : Terminal) : M World I := do
  write (← fields.outStream t) "\x1b[?1l\x1b>"

/--
Julia source: base/Terminals.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval clear(t::UnixTerminal) = write(t.out_stream, $"$(CSI)H$(CSI)2J")
```
-/
def clearUnix {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (write : Stream → String → M World I) (t : Terminal) : M World I := do
  write (← fields.outStream t) "\x1b[H\x1b[2J"

/--
Julia source: base/Terminals.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval clear_line(t::UnixTerminal) = write(t.out_stream, $"\r$(CSI)0K")
```
-/
def clearLineUnix {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (write : Stream → String → M World I) (t : Terminal) : M World I := do
  write (← fields.outStream t) "\r\x1b[0K"

/--
Julia source: base/Terminals.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
beep(t::UnixTerminal) = write(t.err_stream,"\x7")
```
-/
def beepUnix {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (write : Stream → String → M World I) (t : Terminal) : M World I := do
  write (← fields.errStream t) "\x07"

/--
Julia source: base/Terminals.jl:158-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.displaysize(t::UnixTerminal) = displaysize(t.out_stream)::Tuple{Int,Int}
```
-/
def displaysizeUnix {World Terminal Stream : Type} (fields : UnixFields World Terminal Stream)
    (displaysize : Stream → M World (I × I)) (t : Terminal) : M World (I × I) := do
  displaysize (← fields.outStream t)

/--
Julia source: base/Terminals.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hascolor(t::TTYTerminal) = get(t.out_stream, :color, false)::Bool
```
-/
def hascolorTTY {World Stream : Type} (get : Stream → String → Bool → M World Bool)
    (t : TTYTerminal Stream) : M World Bool := get t.out_stream "color" false

/--
Julia source: base/Terminals.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.in(key_value::Pair, t::TTYTerminal) = in(key_value, pipe_writer(t))
```
-/
def containsTTY {World Stream Pair Result : Type}
    (contains : Stream → Pair → M World Result) (t : TTYTerminal Stream) (pair : Pair) : M World Result :=
  contains t.out_stream pair

/--
Julia source: base/Terminals.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.haskey(t::TTYTerminal, key) = haskey(pipe_writer(t), key)
```
-/
def haskeyTTY {World Stream Key Result : Type}
    (contains : Stream → Key → M World Result) (t : TTYTerminal Stream) (key : Key) : M World Result :=
  contains t.out_stream key

/--
Julia source: base/Terminals.jl:165-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.getindex(t::TTYTerminal, key) = getindex(pipe_writer(t), key)
```
-/
def getindexTTY {World Stream Key Result : Type}
    (contains : Stream → Key → M World Result) (t : TTYTerminal Stream) (key : Key) : M World Result :=
  contains t.out_stream key

/--
Julia source: base/Terminals.jl:166-166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.get(t::TTYTerminal, key, default) = get(pipe_writer(t), key, default)
```
-/
def getTTY {World Stream Key Value : Type} (get : Stream → Key → Value → M World Value)
    (t : TTYTerminal Stream) (key : Key) (default : Value) : M World Value :=
  get t.out_stream key default

/--
Julia source: base/Terminals.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.peek(t::TTYTerminal, ::Type{T}) where {T} = peek(t.in_stream, T)::T
```
-/
def peekTTY {World Stream T : Type} (peek : Stream → M World T)
    (t : TTYTerminal Stream) : M World T := peek t.in_stream


/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/Terminals.jl:1-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module Terminals
-- 
-- export
--     AbstractTerminal,
--     TextTerminal,
--     UnixTerminal,
--     TerminalBuffer,
--     TTYTerminal,
--     cmove,
--     cmove_col,
--     cmove_down,
--     cmove_left,
--     cmove_line_down,
--     cmove_line_up,
--     cmove_right,
--     cmove_up,
--     disable_bracketed_paste,
--     enable_bracketed_paste,
--     end_keypad_transmit_mode,
--     getX,
--     getY,
--     hascolor,
--     pos,
--     raw!
-- 
-- import Base:
--     displaysize,
--     flush,
--     pipe_reader,
--     pipe_writer
-- 
-- ## AbstractTerminal: abstract supertype of all terminals ##
-- 
-- /Source

-- Source: base/Terminals.jl:37-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## TextTerminal ##
-- 
-- /Source

-- Source: base/Terminals.jl:41-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Terminal interface:
-- /Source

-- Source: base/Terminals.jl:50-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Relative moves (Absolute position fallbacks)
-- /Source

-- Source: base/Terminals.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:69-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:71-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Defaults
-- /Source

-- Source: base/Terminals.jl:74-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Utility Functions
-- /Source

-- Source: base/Terminals.jl:78-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # For terminals with buffers
-- /Source

-- Source: base/Terminals.jl:81-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:85-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:87-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:89-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # FIXME: Deprecated, unused by Julia itself but kept for packages. Use `REPL.LineEdit.enter_input_mode`/`leave_input_mode`.
-- /Source

-- Source: base/Terminals.jl:92-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## UnixTerminal ##
-- 
-- /Source

-- Source: base/Terminals.jl:96-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:99-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- @nospecialize
-- /Source

-- Source: base/Terminals.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:111-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @specialize
-- 
-- /Source

-- Source: base/Terminals.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:122-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if Sys.iswindows()
-- /Source

-- Source: base/Terminals.jl:142-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- else
-- /Source

-- Source: base/Terminals.jl:146-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- # eval some of these definitions to insert CSI as a constant string
-- /Source

-- Source: base/Terminals.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:157-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:161-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # use cached value of have_color
-- /Source

-- Source: base/Terminals.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/Terminals.jl:169-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end # module
-- /Source


end JuliaLean.base.Terminals

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


end JuliaLean.ShowCov.Terminals


namespace JuliaLean.ShowCov.Methods.TerminalsFile

open JuliaLean.ShowCov.Terminals

def unimplementedUnit : R Unit := textFallbackError
def unimplementedIO : R String := textFallbackError
def unimplementedDims : R (Int × Int) := textFallbackError

def m43 (_t : TextTerm) := unimplementedIO

def m44 (_t : TextTerm) := unimplementedIO

def m45 (_t : TextTerm) := unimplementedDims

def m46 (_t : TextTerm) (_x _y : Int) := unimplementedUnit

def m47 (_t : TextTerm) : R Int := textFallbackError

def m48 (_t : TextTerm) : R Int := textFallbackError

def m49 (t : TextTerm) := pos t

def m52 (t : TextTerm) (n : Int) := cmoveUp t n

def m53 (t : TextTerm) := cmoveUp1 t

def m55 (t : TextTerm) (n : Int) := cmoveDown t n

def m56 (t : TextTerm) := cmoveDown1 t

def m58 (t : TextTerm) (n : Int) := cmoveLeft t n

def m59 (t : TextTerm) := cmoveLeft1 t

def m61 (t : TextTerm) (n : Int) := cmoveRight t n

def m62 (t : TextTerm) := cmoveRight1 t

def m64 (t : TextTerm) (n : Int) := cmoveLineUp t n

def m65 (t : TextTerm) := cmoveLineUp1 t

def m67 (t : TextTerm) (n : Int) := cmoveLineDown t n

def m68 (t : TextTerm) := cmoveLineDown1 t

def m70 (t : TextTerm) (c : Int) := cmoveCol t c

def m73 (t : TextTerm) := hascolorText t

def m76 (t : TextTerm) := width t

def m77 (t : TextTerm) := height t

def m80 (t : TextTerm) := flushText t

def m82 (_t : TextTerm) := unimplementedUnit

def m83 (_t : TextTerm) (_row : Int) := unimplementedUnit

def m84 (_t : TextTerm) := unimplementedUnit

def m86 (_t : TextTerm) (_raw : Bool) := unimplementedUnit

def m88 (t : TextTerm) := beepText t

def m90 (t : TextTerm) := bracketedPasteText t

def m91 (t : TextTerm) := bracketedPasteText t

def m97 {σ} (t : UnixTerm σ) := pipeReaderU t

def m98 {σ} (t : UnixTerm σ) := pipeWriterU t

def m115 (n : Int) := cmoveUpU n

def m116 (n : Int) := cmoveDownU n

def m117 (n : Int) := cmoveRightU n

def m118 (n : Int) := cmoveLeftU n

def m119 (n : Int) := cmoveLineUpU n

def m120 (n : Int) := cmoveLineDownU n

def m121 (n : Int) := cmoveColU n

def m143 (handle : Option Nat) (ccallResult : Int) := rawTTY handle ccallResult

def m149 {sigma} (_t : UnixTerm sigma) := enableBracketedPasteU

def m150 {sigma} (_t : UnixTerm sigma) := disableBracketedPasteU

def m151 {sigma} (_t : UnixTerm sigma) := endKeypadTransmitModeU

def m154 {sigma} (_t : UnixTerm sigma) := clearU

def m155 {sigma} (_t : UnixTerm sigma) := clearLineU

def m156 {sigma} (_t : UnixTerm sigma) := beepU

def m158 {σ} (t : UnixTerm σ) := displaysizeU t

def m160 {σ} (t : UnixTerm σ) := hascolorTTY t

def m163 {σ} (t : UnixTerm σ) (kv : String × String) := inTTY t kv

def m164 {σ} (t : UnixTerm σ) (key : String) := haskeyTTY t key

def m165 {σ} (t : UnixTerm σ) (key : String) := getindexTTY t key

def m166 {σ} (t : UnixTerm σ) (key default : String) := getTTY t key default

def m168 {σ} (t : UnixTerm σ) := peekTTY t

end JuliaLean.ShowCov.Methods.TerminalsFile
