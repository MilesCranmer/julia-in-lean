import JuliaLean.Core
import JuliaLean.ShellCmd.Cmd

/-!
Pure models of the stream, event, and process state transitions in Julia master
`bbfa0ce4150`.

The byte buffer is the logical readable sequence: a `BufferStream`'s in-memory
buffer, a receiving `PipeEndpoint`'s queue after its peer writes, or an
`IOStream`'s file contents after the caller rewinds it. Blocking is abstracted
by considering a state after the corresponding libuv or file operation has
completed.
-/

namespace JuliaLean.Streams

open JuliaLean

inductive StreamKind where
  | ioStream
  | libuvStream
  | bufferStream
  deriving Repr, DecidableEq

inductive StreamStatus where
  | active
  | eof
  | closing
  | closed
  deriving Repr, DecidableEq

structure StreamM where
  kind : StreamKind
  status : StreamStatus
  buffer : List UInt8
  writable : Bool
  deriving Repr, DecidableEq

inductive StreamErr where
  | eofError
  | ioError
  | argumentError
  | invalidPointer
  | methodError
  deriving Repr, DecidableEq

abbrev SR (α : Type) := Except StreamErr α

/-- A newly initialized readable and writable stream. -/
def freshStream (kind : StreamKind) : StreamM :=
  { kind, status := .active, buffer := [], writable := true }

/-- `isopen`, `base/iostream.jl:88`, `base/stream.jl:377-382,2219`. -/
def isOpen (s : StreamM) : Bool := s.status != .closed

/-- `iswritable` checks that an IOStream is open and has a writable access mode
(`base/iostream.jl:104`). -/
def isWritable (s : StreamM) : Bool :=
  match s.kind with
  | .ioStream => isOpen s && s.writable
  | .libuvStream | .bufferStream => isOpen s && s.status != .closing && s.writable

/-- `close`, `base/iostream.jl:90-93`, `base/stream.jl:770-783,2231-2236`. -/
def closeStream (s : StreamM) : StreamM := { s with status := .closed }

/-- `eof`: buffered data prevents EOF even after close (`base/io.jl:208-215`),
as implemented for libuv streams at `base/stream.jl:104-115,2416-2422`. -/
def streamEof (s : StreamM) : Bool :=
  s.buffer.isEmpty && (s.status == .eof || s.status == .closed)

/-- `unsafe_write` and the byte `write` specialization. For a pipe this updates
the connected reader's logical queue; for an `IOStream` it updates the logical
file contents later exposed by rewinding. Closed IOStreams fail the
`iswritable` guard (`base/iostream.jl:411-425`). Libuv-backed methods call
`check_open` (`base/stream.jl:384-388,1736-1739,2404-2413`). -/
def unsafeWrite (s : StreamM) (memory : List UInt8) (n : Nat) : SR (Nat × StreamM) :=
  if n > memory.length then .error .invalidPointer
  else
    match s.kind with
    | .ioStream =>
        if !isWritable s then .error .argumentError
        else .ok (n, { s with buffer := s.buffer ++ memory.take n })
    | .libuvStream =>
        if !isWritable s then .error .ioError
        else .ok (n, s)
    | .bufferStream =>
        if !isWritable s then .error .ioError
        else .ok (n, { s with buffer := s.buffer ++ memory.take n })

def writeBytes (s : StreamM) (bytes : List UInt8) : SR (Nat × StreamM) :=
  unsafeWrite s bytes bytes.length

/-- The two endpoints created by `Pipe()`/`link_pipe!`,
`base/stream.jl:1048-1118`. -/
structure PipeM where
  readEnd : StreamM
  writeEnd : StreamM
  deriving Repr, DecidableEq

def freshPipe : PipeM :=
  { readEnd := freshStream .libuvStream, writeEnd := freshStream .libuvStream }

/-- Writing one PipeEndpoint appends to its connected peer's receive queue. -/
def pipeWrite (p : PipeM) (bytes : List UInt8) : SR (Nat × PipeM) :=
  if !isWritable p.writeEnd then .error .ioError
  else .ok (bytes.length,
    { p with readEnd := { p.readEnd with buffer := p.readEnd.buffer ++ bytes } })

/-- `closewrite(pipe)` closes the writer direction and delivers EOF to the
reader after the queued bytes, `base/stream.jl:719-747,1076`. -/
def closePipeWrite (p : PipeM) : PipeM :=
  { readEnd := { p.readEnd with status := .eof },
    writeEnd := { p.writeEnd with writable := false } }

/-- Exact-length `unsafe_read`, `base/iostream.jl:477-483` and
`base/stream.jl:1240-1275,2249-2255`. -/
def unsafeRead (s : StreamM) (n : Nat) : SR (List UInt8 × StreamM) :=
  if n ≤ s.buffer.length then
    .ok (s.buffer.take n, { s with buffer := s.buffer.drop n })
  else .error .eofError

/-- `readavailable`, `base/iostream.jl:431-442` and
`base/stream.jl:1292-1300,2277-2287`. -/
def readAvailable (s : StreamM) : SR (List UInt8 × StreamM) :=
  .ok (s.buffer, { s with buffer := [] })

structure DelimSplit where
  before : List UInt8
  found : Bool
  after : List UInt8
  deriving Repr, DecidableEq

/-- Split at the first delimiter, consuming it when present. -/
def splitUntil (delim : UInt8) : List UInt8 → DelimSplit
  | [] => ⟨[], false, []⟩
  | b :: bs =>
      if b == delim then ⟨[], true, bs⟩
      else
        let r := splitUntil delim bs
        ⟨b :: r.before, r.found, r.after⟩

/-- `readuntil`/`copyuntil` delimiter handling for a completed read,
`base/stream.jl:1302-1344,2339-2360` and `base/iostream.jl:490-503`. -/
def readUntil (s : StreamM) (delim : UInt8) (keep : Bool) : SR (List UInt8 × StreamM) :=
  let r := splitUntil delim s.buffer
  let bytes := if r.found && keep then r.before ++ [delim] else r.before
  .ok (bytes, { s with buffer := r.after })

def stripTrailingCR (bytes : List UInt8) : List UInt8 :=
  match bytes.reverse with
  | 13 :: rest => rest.reverse
  | _ => bytes

/-- `readline`, including CRLF removal, `base/io.jl:668-716` and
`base/iostream.jl:505-508`. -/
def readLine (s : StreamM) (keep : Bool) : SR (List UInt8 × StreamM) :=
  let r := splitUntil 10 s.buffer
  let bytes :=
    if keep && r.found then r.before ++ [10]
    else if r.found then stripTrailingCR r.before
    else r.before
  .ok (bytes, { s with buffer := r.after })

/-! ## Timer and AsyncCondition -/

inductive EventKind where
  | oneShotTimer
  | repeatingTimer
  | asyncCondition
  deriving Repr, DecidableEq

structure EventM where
  kind : EventKind
  isopen : Bool
  set : Bool
  deriving Repr, DecidableEq

def freshEvent (kind : EventKind) : EventM := ⟨kind, true, false⟩

/-- `close(::Union{Timer,AsyncCondition})`, `base/asyncevent.jl:257-292`. -/
def closeEvent (e : EventM) : EventM := { e with isopen := false }

/-- libuv notification callbacks, `base/asyncevent.jl:328-358`. A one-shot
timer becomes inactive while preserving its triggered bit. -/
def signalEvent (e : EventM) : EventM :=
  if !e.isopen then e
  else match e.kind with
    | .oneShotTimer => { e with isopen := false, set := true }
    | .repeatingTimer | .asyncCondition => { e with set := true }

/-- `_trywait` followed by `wait`, `base/asyncevent.jl:177-243`. Master keeps
the set bit on a one-shot timer, so later waits also return. -/
def waitEvent (e : EventM) : SR EventM :=
  if e.set then
    .ok (if e.kind == .oneShotTimer then e else { e with set := false })
  else if !e.isopen then .error .eofError
  else .error .ioError

/-! ## Commands and processes -/

abbrev CmdM := JuliaLean.ShellCmd.CmdM

inductive CommandM where
  | leaf (cmd : CmdM)
  | stdoutPipe (left right : CommandM)
  | stderrPipe (left right : CommandM)
  | concurrent (left right : CommandM)
  | redirect (cmd : CommandM)
  deriving Repr, DecidableEq

inductive ProcessErr where
  | methodError
  | processFailed (processes : List Nat)
  deriving Repr, DecidableEq

abbrev PR (α : Type) := Except ProcessErr α

/-- `pipeline(a,b,c...)` is a left fold, `base/cmd.jl:543-576`. -/
def pipelineMany (first : CommandM) (rest : List CommandM) : CommandM :=
  rest.foldl .stdoutPipe first

/-- `ignorestatus`, `base/cmd.jl:297-305`. Master omits `ErrOrCmds`, the
constructor represented by `stderrPipe`. -/
def ignoreStatus : CommandM → PR CommandM
  | .leaf cmd => .ok (.leaf { cmd with ignorestatus := true })
  | .stdoutPipe a b => do return .stdoutPipe (← ignoreStatus a) (← ignoreStatus b)
  | .concurrent a b => do return .concurrent (← ignoreStatus a) (← ignoreStatus b)
  | .redirect cmd => do return .redirect (← ignoreStatus cmd)
  | .stderrPipe _ _ => .error .methodError

def detachedFlag : UInt32 := 8

/-- `detach(::Cmd)`, `base/cmd.jl:308-312`. -/
def detachCmd (cmd : CmdM) : CmdM := { cmd with flags := cmd.flags ||| detachedFlag }

/-- Public `detach(command)`. Master defines only the leaf `Cmd` method. -/
def detachCommand : CommandM → PR CommandM
  | .leaf cmd => .ok (.leaf (detachCmd cmd))
  | _ => .error .methodError

structure ProcessM where
  id : Nat
  exited : Bool
  exitcode : JInt .i64
  termsignal : JInt .i32
  ignorestatus : Bool
  deriving Repr, DecidableEq

/-- `test_success`, `base/process.jl:593-600`. -/
def testSuccess (p : ProcessM) : Bool :=
  p.exited && p.exitcode.val == 0 && p.termsignal.val == 0

inductive ProcessStatus where
  | running
  | exited (code : Int)
  | signaled (signal : Int)
  deriving Repr, DecidableEq

/-- `process_status`, `base/process.jl:730-736`. -/
def processStatus (p : ProcessM) : ProcessStatus :=
  if !p.exited then .running
  else if p.termsignal.val > 0 then .signaled p.termsignal.val
  else .exited p.exitcode.val

/-- Processes placed in `ProcessFailedException`, `base/process.jl:656-665`. -/
def failedProcesses (ps : List ProcessM) : List ProcessM :=
  ps.filter (fun p => !testSuccess p && !p.ignorestatus)

def pipelineError (ps : List ProcessM) : PR Unit :=
  match failedProcesses ps with
  | [] => .ok ()
  | failed => .error (.processFailed (failed.map (·.id)))

/-- `run(...; wait=true)`, `base/process.jl:553-579`. -/
def runResult (ps : List ProcessM) : PR Unit :=
  if ps.all testSuccess then .ok () else pipelineError ps

/-- `read(cmd)`, `base/process.jl:515-521`: output is returned only when the
same status check as `run` succeeds or all failures are ignored. -/
def readCommand (output : List UInt8) (ps : List ProcessM) : PR (List UInt8) :=
  match runResult ps with
  | .ok _ => .ok output
  | .error e => .error e

/-- `kill`, followed by the libuv exit callback, `base/process.jl:63-78,675-685`.
Killing an exited process is a successful no-op. -/
def killProcess (p : ProcessM) (signal : JInt .i32) : ProcessM :=
  if p.exited then p
  else { p with exited := true, exitcode := JInt.lit .i64 0, termsignal := signal }

end JuliaLean.Streams
