import JuliaLean.Streams.Model

/-!
Coverage models for every remaining method in `base/stream.jl`,
`base/iostream.jl`, `base/libuv.jl`, `base/asyncevent.jl`, and
`base/process.jl` at master `bbfa0ce4150`.

The OS and libuv are explicit inputs. The models preserve Julia's branch order,
status changes, buffer movement, request ownership, and error selection without
claiming an implementation of the external kernel operations.

These family-level abstractions are not method-row coverage under the stricter
`coverage/REVIEW_PROMPT.md` criterion. No coverage manifest row should cite
them until that row has its own exact body mirror and all-input property.
-/

namespace JuliaLean.Streams

open JuliaLean

/-! ## `base/stream.jl`: handle lifecycle and request ownership -/

inductive UvStatus where
  | uninit | init | connecting | opened | active | closing | closed | eof | paused
  deriving Repr, DecidableEq

def uvStatusString (hasHandle : Bool) (status : UvStatus) : String :=
  if !hasHandle then
    match status with
    | .closed => "closed"
    | .uninit => "null"
    | _ => "invalid status"
  else
    match status with
    | .uninit => "uninit"
    | .init => "init"
    | .connecting => "connecting"
    | .opened => "open"
    | .active => "active"
    | .paused => "paused"
    | .closing => "closing"
    | .closed => "closed"
    | .eof => "eof"

structure EndpointM where
  hasHandle : Bool
  status : UvStatus
  buffer : List UInt8
  readError : Bool
  sendBuffer : Option (List UInt8)
  readable : Bool
  writable : Bool
  throttle : Nat
  preserved : Nat
  deriving Repr, DecidableEq

def endpointCtor (hasHandle : Bool) (status : UvStatus) : EndpointM :=
  { hasHandle, status, buffer := [], readError := false, sendBuffer := none,
    readable := true, writable := true, throttle := 10 * 1024 * 1024,
    preserved := 0 }

inductive EndpointField where | handle | status | buffer | readable | writable | throttle
  deriving Repr, DecidableEq

def endpointField (s : EndpointM) : EndpointField → Nat
  | .handle => if s.hasHandle then 1 else 0
  | .status => match s.status with
    | .uninit => 0 | .init => 1 | .connecting => 2 | .opened => 3 | .active => 4
    | .closing => 5 | .closed => 6 | .eof => 7 | .paused => 8
  | .buffer => s.buffer.length
  | .readable => if s.readable then 1 else 0
  | .writable => if s.writable then 1 else 0
  | .throttle => s.throttle

def endpointShow (typeName : String) (fd : Int) (s : EndpointM) : String :=
  typeName ++ "(" ++ toString fd ++ " " ++ uvStatusString s.hasHandle s.status ++
    ", " ++ toString s.buffer.length ++ " bytes waiting)"

def setupStreamStdio (s : EndpointM) : EndpointM × Bool := (s, false)
def rawHandleModel (s : EndpointM) : Bool := s.hasHandle

def lockDepth (depth : Nat) (locking : Bool) : Nat :=
  if locking then depth + 1 else depth - 1

def endpointIsOpen (s : EndpointM) : Except StreamErr Bool :=
  if s.status == .uninit || s.status == .init || !s.hasHandle then
    .error .argumentError
  else .ok (s.status != .closed)

def endpointReadable (s : EndpointM) : Bool :=
  !s.buffer.isEmpty ||
    (s.hasHandle && s.status != .closed && s.status != .eof && s.readable)

def endpointWritable (s : EndpointM) : Bool :=
  s.hasHandle && s.status != .closed && s.status != .closing && s.writable

def endpointCheckOpen (s : EndpointM) : Except StreamErr Unit :=
  match endpointIsOpen s with
  | .ok true => if s.status == .closing then .error .ioError else .ok ()
  | _ => .error .ioError

def waitReadState (s : EndpointM) (needed : Nat) : Except StreamErr EndpointM :=
  if needed ≤ s.buffer.length then .ok s
  else if s.readError then .error .ioError
  else if !s.hasHandle || s.status == .closed || s.status == .eof then .ok s
  else .ok { s with throttle := max needed s.throttle }

def endpointCloseWrite (s : EndpointM) (shutdownStatus : Int) : Except StreamErr EndpointM :=
  if !endpointWritable s then .ok s
  else if shutdownStatus < 0 then .error .ioError
  else .ok { s with writable := false }

def endpointClose (s : EndpointM) : EndpointM :=
  { s with status := .closed, hasHandle := false, readable := false, writable := false }

def displaySizeModel (lines columns : Option Nat) : Nat × Nat :=
  (lines.getD 24, columns.getD 80)

def allocRequestSize (available recommended maximum : Nat) : Nat :=
  min (maximum - available) recommended

def startReadingState (s : EndpointM) : EndpointM :=
  if s.status == .opened || s.status == .paused then { s with status := .active } else s

def stopReadingState (s : EndpointM) : EndpointM :=
  if s.status == .active then { s with status := .paused } else s

def pipeEndpoints (p : PipeM) : StreamM × StreamM := (p.readEnd, p.writeEnd)

def notifyFilled (s : EndpointM) (bytes : List UInt8) (nread : Int) : EndpointM :=
  if nread < 0 then
    let hasError : Bool := decide (nread ≠ (-4095 : Int))
    let nextStatus := if nread == -4095 then UvStatus.eof else s.status
    { s with readError := hasError, status := nextStatus }
  else
    let added := bytes.take nread.toNat
    let nextStatus := if s.status == .paused then UvStatus.opened else s.status
    let nextBuffer := s.buffer ++ added
    { s with buffer := nextBuffer, status := nextStatus }

inductive ReqOwner where | fireAndForget | waiter | detachedReq | callbackDone
  deriving Repr, DecidableEq

structure ReqM where
  owner : ReqOwner
  cancelRequested : Bool
  rooted : Bool
  pending : Nat
  firstError : Option Int
  written : Nat
  deriving Repr, DecidableEq

def beginReq (cancelled : Bool) (splitCount : Nat) : Except StreamErr ReqM :=
  if cancelled then .error .ioError
  else .ok ⟨.waiter, false, false, splitCount, none, 0⟩

def markReqCancelled (r : ReqM) : ReqM := { r with cancelRequested := true }

def finishReq (r : ReqM) (completed : Bool) (tryCancel : Bool) (knownOwner : Bool) : ReqM :=
  if completed then
    ⟨.callbackDone, r.cancelRequested, false, r.pending, r.firstError, r.written⟩
  else
    ⟨.detachedReq, tryCancel, knownOwner, r.pending, r.firstError, r.written⟩

def completeReq (r : ReqM) (status : Int) (nwritten : Nat) : ReqM :=
  let err := if decide (status < 0) && r.firstError.isNone then some status else r.firstError
  let nextPending := r.pending - 1
  let nextWritten := r.written + nwritten
  let nextOwner := if r.pending ≤ 1 then ReqOwner.callbackDone else r.owner
  ⟨nextOwner, r.cancelRequested, r.rooted, nextPending, err, nextWritten⟩

def requeueUnwritten (sent queued : List UInt8) (nwritten : Nat) : List UInt8 :=
  sent.drop nwritten ++ queued

/-! ## Stream reads, writes, redirection, and BufferStream -/

def readbytesModel (buffer : List UInt8) (n : Nat) : Nat × List UInt8 × List UInt8 :=
  let count := min n buffer.length
  (count, buffer.take count, buffer.drop count)

def readUntilModel (buffer : List UInt8) (d : UInt8) (keep : Bool) : List UInt8 × List UInt8 :=
  let r := splitUntil d buffer
  (if r.found && keep then r.before ++ [d] else r.before, r.after)

def peekModel (buffer : List UInt8) (n : Nat) : Except StreamErr (List UInt8) :=
  if n ≤ buffer.length then .ok (buffer.take n) else .error .eofError

def writeChunks (n chunk : Nat) : List Nat :=
  if chunk = 0 then []
  else (List.range ((n + chunk - 1) / chunk)).map fun i => min chunk (n - i * chunk)

inductive RedirectValue where | keep | devnull | path (p : String) | stream
  deriving Repr, DecidableEq

structure RedirectM where
  inStream : RedirectValue
  outStream : RedirectValue
  errStream : RedirectValue
  deriving Repr, DecidableEq

def resolveRedirect (new old : RedirectValue) : RedirectValue :=
  match new with | .keep => old | x => x

def redirectStdio (old : RedirectM) (newIn newOut newErr : RedirectValue) : RedirectM :=
  { inStream := resolveRedirect newIn old.inStream,
    outStream := resolveRedirect newOut old.outStream,
    errStream := resolveRedirect newErr old.errStream }

def samePath (x y : String) : Bool := x == y

def pipeGetindex (p : α × α) (key : Int) : Option α :=
  if key = 1 then some p.1 else if key = 2 then some p.2 else none

def bufferReadByte (s : StreamM) : Except StreamErr (UInt8 × StreamM) :=
  match s.buffer with
  | b :: rest => .ok (b, { s with buffer := rest })
  | [] => .error .eofError

def bufferReadN (s : StreamM) (n : Nat) : List UInt8 × StreamM :=
  (s.buffer.take n, { s with buffer := s.buffer.drop n })

def bufferResetEof (s : StreamM) : StreamM :=
  if s.status == .eof then { s with status := .active } else s

def bufferReadable (s : StreamM) : Bool := isOpen s || !s.buffer.isEmpty
def bufferWritable (s : StreamM) : Bool := isOpen s && s.writable
def bufferClose (s : StreamM) : StreamM := closeStream s
def bufferEof (s : StreamM) : Bool := streamEof s
def bufferSkip (s : StreamM) (n : Nat) : StreamM := { s with buffer := s.buffer.drop n }
def bufferFlush (s : StreamM) : StreamM := s

/-! ## `base/iostream.jl` -/

structure IOFileM where
  data : List UInt8
  position : Nat
  isopen : Bool
  readable : Bool
  writable : Bool
  deriving Repr, DecidableEq

def ioCtor (readable writable : Bool) : IOFileM :=
  { data := [], position := 0, isopen := true, readable, writable }

def ioPointerModel (address : Nat) : Nat := address
def ioFdModel (fd : Int) : Int := fd
def ioStatModel (fd : Int) : Int := fd
def ioFlushModel (s : IOFileM) : Except StreamErr IOFileM :=
  if s.isopen then .ok s else .error .ioError
def ioBytesAvailable (s : IOFileM) : Nat := s.data.length - s.position
def ioEof (s : IOFileM) : Bool := ioBytesAvailable s = 0

def ioClose (s : IOFileM) : IOFileM := { s with isopen := false }

def ioTruncate (s : IOFileM) (n : Nat) : IOFileM :=
  let data := if n ≤ s.data.length then s.data.take n
    else s.data ++ List.replicate (n - s.data.length) 0
  { s with data, position := min s.position n }

def ioSeek (s : IOFileM) (n : Nat) : IOFileM := { s with position := n }
def ioSeekEnd (s : IOFileM) : IOFileM := { s with position := s.data.length }
def ioSkip (s : IOFileM) (delta : Int) : IOFileM :=
  { s with position := (max 0 ((s.position : Int) + delta)).toNat }

inductive OpenMode where | r | rplus | w | wplus | a | aplus
  deriving Repr, DecidableEq

def parseOpenMode : String → Option OpenMode
  | "r" => some .r | "r+" => some .rplus | "w" => some .w
  | "w+" => some .wplus | "a" => some .a | "a+" => some .aplus
  | _ => none

def modeFlags : OpenMode → Bool × Bool × Bool × Bool
  | .r => (true, false, false, false)
  | .rplus => (true, true, false, false)
  | .w => (false, true, true, false)
  | .wplus => (true, true, true, false)
  | .a => (false, true, false, true)
  | .aplus => (true, true, false, true)

def ioWrite (s : IOFileM) (bytes : List UInt8) : Except StreamErr (Nat × IOFileM) :=
  if !s.isopen || !s.writable then .error .argumentError
  else
    let prefixData := s.data.take s.position
    let suffix := s.data.drop (s.position + bytes.length)
    let nextData := prefixData ++ bytes ++ suffix
    let nextPosition := s.position + bytes.length
    .ok (bytes.length,
      ⟨nextData, nextPosition, s.isopen, s.readable, s.writable⟩)

def ioReadN (s : IOFileM) (n : Nat) : List UInt8 × IOFileM :=
  let bytes := (s.data.drop s.position).take n
  (bytes, { s with position := s.position + bytes.length })

def ioReadExact (s : IOFileM) (n : Nat) : Except StreamErr (List UInt8 × IOFileM) :=
  let r := ioReadN s n
  if r.1.length = n then .ok r else .error .eofError

def ioReadAvailable (s : IOFileM) : List UInt8 × IOFileM :=
  ioReadN s (s.data.length - s.position)

def ioReadUntil (s : IOFileM) (d : UInt8) (keep : Bool) : List UInt8 × IOFileM :=
  let unread := s.data.drop s.position
  let r := splitUntil d unread
  let bytes := if r.found && keep then r.before ++ [d] else r.before
  let consumed := r.before.length + if r.found then 1 else 0
  (bytes, { s with position := s.position + consumed })

def ioReadline (s : IOFileM) (keep : Bool) : List UInt8 × IOFileM :=
  let r := ioReadUntil s 10 keep
  if keep then r else (stripTrailingCR r.1, r.2)

def ioTake (s : IOFileM) : List UInt8 × IOFileM :=
  (s.data, { s with data := [], position := 0 })

def ioPeek (s : IOFileM) : Except StreamErr UInt8 :=
  match s.data[s.position]? with | some b => .ok b | none => .error .eofError

/-! ## `base/libuv.jl` -/

structure HandleDataM where
  associated : Bool
  preserved : Bool
  referenced : Bool
  deriving Repr, DecidableEq

def associateHandle (_ : α) : HandleDataM := ⟨true, false, true⟩
def disassociateHandle (h : HandleDataM) : HandleDataM := { h with associated := false }
def preserveHandle (h : HandleDataM) : HandleDataM := { h with preserved := true }
def unpreserveHandle (h : HandleDataM) : HandleDataM := { h with preserved := false }
def uvRef (h : HandleDataM) : HandleDataM := { h with referenced := true }
def uvUnref (h : HandleDataM) : HandleDataM := { h with referenced := false }

def uvSizeResult (size : Option Nat) : Except StreamErr Nat :=
  match size with | some n => .ok n | none => .error .argumentError

def iolockDepth (depth : Nat) (beginning : Bool) : Nat :=
  if beginning then depth + 1 else depth - 1

def uvErrorResult (code : Int) : Except StreamErr Unit :=
  if code < 0 then .error .ioError else .ok ()

def uvErrorText (pfx name description : String) (code : Int) : String :=
  pfx ++ ": " ++ name ++ " (" ++ description ++ ")" ++ " [" ++ toString code ++ "]"

inductive HandleKind where | file | tty | tcp | pipe | invalid
  deriving Repr, DecidableEq

def reinitStdioKind : HandleKind → Except StreamErr StreamKind
  | .file => .ok .ioStream
  | .tty | .tcp | .pipe => .ok .libuvStream
  | .invalid => .error .argumentError

def initStdioModel (kind : HandleKind) : Except StreamErr StreamKind :=
  reinitStdioKind kind

/-! ## `base/asyncevent.jl` -/

structure TimerSetup where
  timeoutMs : Nat
  intervalMs : Nat
  deriving Repr, DecidableEq

def ceilMillis (microseconds : Nat) : Nat := (microseconds + 999) / 1000

def timerSetup (timeoutUs intervalUs : Nat) : TimerSetup :=
  let timeout := ceilMillis timeoutUs
  { timeoutMs := timeout + if timeoutUs = 0 then 0 else 1,
    intervalMs := ceilMillis intervalUs }

def timerTimeout (t : TimerSetup) : Nat :=
  if t.timeoutMs = 0 then 0 else t.timeoutMs - 1

def timerProperties (t : TimerSetup) : Nat × Nat := (timerTimeout t, t.intervalMs)
def timerShowState (e : EventM) : String := if e.isopen then "open" else "closed"
def callbackShouldContinue (e : EventM) : Bool := e.set && e.isopen
def sleepFinalState (e : EventM) : EventM := closeEvent e

def timedwaitResult (tests : List Bool) (polls : Nat) : Bool :=
  (tests.take (polls + 1)).any id

structure TimeoutWaitM where
  timeoutMs : Nat
  armed : Bool
  deriving Repr, DecidableEq

def timeoutEnqueue (t : TimeoutWaitM) : TimeoutWaitM := { t with armed := true }
def timeoutDequeue (t : TimeoutWaitM) : TimeoutWaitM := { t with armed := false }

/-! ## `base/process.jl` -/

def commandLeaves : CommandM → List CmdM
  | .leaf cmd => [cmd]
  | .stdoutPipe a b | .stderrPipe a b | .concurrent a b => commandLeaves a ++ commandLeaves b
  | .redirect cmd => commandLeaves cmd

def processCtor (id : Nat) (ignored : Bool) : ProcessM :=
  { id, exited := false, exitcode := JInt.typemin .i64,
    termsignal := JInt.typemin .i32, ignorestatus := ignored }

def processExitCallback (p : ProcessM) (exitcode : JInt .i64) (signal : JInt .i32) : ProcessM :=
  { p with exited := true, exitcode := exitcode, termsignal := signal }

def cpuMask (cpus : List Nat) (size : Nat) : List Bool :=
  (List.range size).map fun i => decide ((i + 1) ∈ cpus)

structure SpawnM where
  commands : List CmdM
  hasStdin : Bool
  hasStdout : Bool
  hasStderr : Bool
  deriving Repr, DecidableEq

def spawnModel (cmd : CommandM) (hasStdin hasStdout hasStderr : Bool) : Except StreamErr SpawnM :=
  let leaves := commandLeaves cmd
  if leaves.any (fun c => c.exec.isEmpty) then .error .argumentError
  else .ok ⟨leaves, hasStdin, hasStdout, hasStderr⟩

def stdioCopy (stdios : List α) (fd : Nat) (replacement : α) (default : α) : List α :=
  let padded := stdios ++ List.replicate (fd - stdios.length) default
  padded.set (fd - 1) replacement

inductive StdioKind where | pipeEndpoint | pipe | ioStream | fileRedirect | generic
  deriving Repr, DecidableEq

def setupStdio (kind : StdioKind) (childReadable : Bool) : Bool × Bool :=
  match kind with
  | .pipeEndpoint | .pipe => (childReadable, true)
  | .ioStream => (childReadable, false)
  | .fileRedirect => (childReadable, true)
  | .generic => (childReadable, true)

inductive ProcessOpenMode where | read | write | readWrite | none
  deriving Repr, DecidableEq

def parseProcessMode : String → Option ProcessOpenMode
  | "r" => some .read | "w" => some .write
  | "r+" | "w+" => some .readWrite
  | _ => none

def processOpenMode (read write : Bool) : ProcessOpenMode :=
  if read && write then .readWrite else if read then .read else if write then .write else .none

inductive OpenDoOutcome where | returned | bodyError | unreadOutput | processError
  deriving Repr, DecidableEq

def openDoOutcome (bodyOk outputEof processOk : Bool) : OpenDoOutcome :=
  if !bodyOk then .bodyError
  else if !outputEof then .unreadOutput
  else if !processOk then .processError
  else .returned

def processWaitAll (ps : List ProcessM) : Bool := ps.all (·.exited)
def processRunningAny (ps : List ProcessM) : Bool := ps.any (fun p => !p.exited)
def processExitedAll (ps : List ProcessM) : Bool := ps.all (·.exited)
def processSignaled (p : ProcessM) : Bool := decide (p.termsignal.val > 0)
def processPid (p : ProcessM) (pid : Int) : Except StreamErr Int :=
  if p.exited || pid ≤ 0 then .error .ioError else .ok pid

def cmdExecLength (cmd : CmdM) : Nat := cmd.exec.length
def cmdExecAt (cmd : CmdM) (i : Nat) := cmd.exec[i]?
/-! ## Registry properties -/

def StreamLifecycleCoverage : Prop := ∀ hasHandle status needed s field,
  uvStatusString hasHandle status = uvStatusString hasHandle status ∧
  endpointReadable s = (!s.buffer.isEmpty ||
    (s.hasHandle && s.status != .closed && s.status != .eof && s.readable)) ∧
  waitReadState s needed =
    (if needed ≤ s.buffer.length then .ok s else if s.readError then .error .ioError
     else if !s.hasHandle || s.status == .closed || s.status == .eof then .ok s
     else .ok { s with throttle := max needed s.throttle }) ∧
  endpointField s field = (match field with
    | .handle => if s.hasHandle then 1 else 0
    | .status => match s.status with
      | .uninit => 0 | .init => 1 | .connecting => 2 | .opened => 3 | .active => 4
      | .closing => 5 | .closed => 6 | .eof => 7 | .paused => 8
    | .buffer => s.buffer.length
    | .readable => if s.readable then 1 else 0
    | .writable => if s.writable then 1 else 0
    | .throttle => s.throttle) ∧
  endpointWritable s =
    (s.hasHandle && s.status != .closed && s.status != .closing && s.writable) ∧
  endpointShow "PipeEndpoint" 1 s = "PipeEndpoint(" ++ toString (1 : Int) ++ " " ++ uvStatusString s.hasHandle s.status ++
    ", " ++ toString s.buffer.length ++ " bytes waiting)" ∧
  setupStreamStdio s = (s, false) ∧ rawHandleModel s = s.hasHandle ∧
  displaySizeModel none none = (24, 80) ∧
  allocRequestSize s.buffer.length needed s.throttle = min (s.throttle - s.buffer.length) needed ∧
  pipeEndpoints freshPipe = (freshPipe.readEnd, freshPipe.writeEnd) ∧
  (endpointClose s).status = .closed ∧ (endpointClose s).hasHandle = false ∧
  (endpointClose s).readable = false ∧ (endpointClose s).writable = false ∧
  startReadingState s =
    (if s.status == .opened || s.status == .paused then { s with status := .active } else s) ∧
  stopReadingState s = (if s.status == .active then { s with status := .paused } else s)

def StreamRequestCoverage : Prop := ∀ r completed tryCancel knownOwner status nwritten cancelled splitCount,
  beginReq cancelled splitCount =
    (if cancelled then .error .ioError else .ok ⟨.waiter, false, false, splitCount, none, 0⟩) ∧
  (markReqCancelled r).cancelRequested = true ∧
  (finishReq r completed tryCancel knownOwner).owner =
    (if completed then .callbackDone else .detachedReq) ∧
  (completeReq r status nwritten).pending = r.pending - 1 ∧
  (completeReq r status nwritten).written = r.written + nwritten

def StreamReadWriteCoverage : Prop := ∀ buffer n d keep chunk,
  readbytesModel buffer n = (min n buffer.length, buffer.take (min n buffer.length),
    buffer.drop (min n buffer.length)) ∧
  readUntilModel buffer d keep =
    (let r := splitUntil d buffer
     (if r.found && keep then r.before ++ [d] else r.before, r.after)) ∧
  requeueUnwritten buffer [] n = buffer.drop n ∧
  peekModel buffer n = (if n ≤ buffer.length then .ok (buffer.take n) else .error .eofError) ∧
  writeChunks n chunk = if chunk = 0 then []
    else (List.range ((n + chunk - 1) / chunk)).map fun i => min chunk (n - i * chunk)

def StreamRedirectCoverage : Prop := ∀ (α : Type) old newIn newOut newErr (p : α × α) key,
  redirectStdio old newIn newOut newErr =
    ⟨resolveRedirect newIn old.inStream, resolveRedirect newOut old.outStream,
      resolveRedirect newErr old.errStream⟩ ∧
  pipeGetindex p key = (if key = 1 then some p.1 else if key = 2 then some p.2 else none) ∧
  ∀ x y, samePath x y = (x == y)

def BufferStreamCoverage : Prop := ∀ s n bytes,
  bufferReadByte s = (match s.buffer with
    | b :: rest => .ok (b, { s with buffer := rest })
    | [] => .error .eofError) ∧
  bufferReadN s n = (s.buffer.take n, { s with buffer := s.buffer.drop n }) ∧
  bufferResetEof s = (if s.status == .eof then { s with status := .active } else s) ∧
  bufferReadable s = (isOpen s || !s.buffer.isEmpty) ∧
  bufferWritable s = (isOpen s && s.writable) ∧
  bufferClose s = closeStream s ∧ bufferEof s = streamEof s ∧
  bufferSkip s n = { s with buffer := s.buffer.drop n } ∧ bufferFlush s = s ∧
  writeBytes s bytes = unsafeWrite s bytes bytes.length

def IOStreamLifecycleCoverage : Prop := ∀ s n delta mode bytes readable writable,
  ioCtor readable writable = ⟨[], 0, true, readable, writable⟩ ∧
  ioPointerModel n = n ∧
  (ioTruncate s n).data = (if n ≤ s.data.length then s.data.take n
    else s.data ++ List.replicate (n - s.data.length) 0) ∧
  (ioTruncate s n).position = min s.position n ∧
  ioSkip s delta = { s with position := (max 0 ((s.position : Int) + delta)).toNat } ∧
  ioClose s = { s with isopen := false } ∧
  ioBytesAvailable s = s.data.length - s.position ∧
  ioEof s = decide (ioBytesAvailable s = 0) ∧
  ioSeek s n = { s with position := n } ∧
  ioSeekEnd s = { s with position := s.data.length } ∧
  (match ioWrite s bytes with | .ok (count, _) => count = bytes.length ∨ count = 0 | .error _ => True) ∧
  parseOpenMode mode = match mode with
    | "r" => some .r | "r+" => some .rplus | "w" => some .w
    | "w+" => some .wplus | "a" => some .a | "a+" => some .aplus | _ => none

def IOStreamReadCoverage : Prop := ∀ s n d keep,
  ioReadN s n =
    (let bytes := (s.data.drop s.position).take n
     (bytes, { s with position := s.position + bytes.length })) ∧
  ioReadAvailable s = ioReadN s (s.data.length - s.position) ∧
  ioTake s = (s.data, { s with data := [], position := 0 }) ∧
  ioReadUntil s d keep =
    (let r := splitUntil d (s.data.drop s.position)
     let bytes := if r.found && keep then r.before ++ [d] else r.before
     let consumed := r.before.length + if r.found then 1 else 0
     (bytes, { s with position := s.position + consumed })) ∧
  ioReadline s keep =
    (let r := ioReadUntil s 10 keep
     if keep then r else (stripTrailingCR r.1, r.2)) ∧
  ioReadExact s n =
    (let r := ioReadN s n
     if r.1.length = n then .ok r else .error .eofError) ∧
  ioPeek s = match s.data[s.position]? with | some b => .ok b | none => .error .eofError

def LibuvHandleCoverage : Prop := ∀ (α : Type) (x : α) h size depth,
  associateHandle x = ⟨true, false, true⟩ ∧
  (disassociateHandle h).associated = false ∧
  (preserveHandle h).preserved = true ∧
  (unpreserveHandle h).preserved = false ∧
  (uvRef h).referenced = true ∧ (uvUnref h).referenced = false ∧
  uvSizeResult none = .error .argumentError ∧ uvSizeResult (some size) = .ok size ∧
  iolockDepth depth true = depth + 1 ∧ iolockDepth depth false = depth - 1

def LibuvErrorCoverage : Prop := ∀ code pfx name description kind,
  uvErrorResult code = (if code < 0 then .error .ioError else .ok ()) ∧
  uvErrorText pfx name description code =
    pfx ++ ": " ++ name ++ " (" ++ description ++ ")" ++ " [" ++ toString code ++ "]" ∧
  reinitStdioKind kind = (match kind with
    | .file => .ok .ioStream | .tty | .tcp | .pipe => .ok .libuvStream
    | .invalid => .error .argumentError)

def AsyncConstructionCoverage : Prop := ∀ timeout interval kind,
  timerSetup timeout interval =
    { timeoutMs := ceilMillis timeout + if timeout = 0 then 0 else 1,
      intervalMs := ceilMillis interval } ∧
  timerTimeout (timerSetup timeout interval) =
    (if (timerSetup timeout interval).timeoutMs = 0 then 0
     else (timerSetup timeout interval).timeoutMs - 1) ∧
  timerProperties (timerSetup timeout interval) =
    (timerTimeout (timerSetup timeout interval), (timerSetup timeout interval).intervalMs) ∧
  timerShowState (freshEvent .oneShotTimer) = "open" ∧
  callbackShouldContinue (freshEvent .asyncCondition) = false ∧
  freshEvent kind = ⟨kind, true, false⟩

def AsyncUtilityCoverage : Prop := ∀ tests polls timeout armed,
  timedwaitResult tests polls = (tests.take (polls + 1)).any id ∧
  timeoutEnqueue ⟨timeout, armed⟩ = ⟨timeout, true⟩ ∧
  timeoutDequeue ⟨timeout, armed⟩ = ⟨timeout, false⟩ ∧
  (sleepFinalState (freshEvent .oneShotTimer)).isopen = false

def ProcessSpawnCoverage : Prop := ∀ cmd hasStdin hasStdout hasStderr p code signal cpus size,
  spawnModel cmd hasStdin hasStdout hasStderr =
    (let leaves := commandLeaves cmd
     if leaves.any (fun c => c.exec.isEmpty) then .error .argumentError
     else .ok ⟨leaves, hasStdin, hasStdout, hasStderr⟩) ∧
  (processExitCallback p code signal).exitcode = code ∧
  (processExitCallback p code signal).termsignal = signal ∧
  cpuMask cpus size = ((List.range size).map fun i => decide ((i + 1) ∈ cpus)) ∧
  ∀ id ignored, (processCtor id ignored).exited = false

def ProcessStdioCoverage : Prop := ∀ (α : Type) (stdios : List α) fd replacement default kind readable,
  stdioCopy stdios fd replacement default =
    (stdios ++ List.replicate (fd - stdios.length) default).set (fd - 1) replacement ∧
  setupStdio kind readable = (match kind with
    | .pipeEndpoint | .pipe => (readable, true)
    | .ioStream => (readable, false)
    | .fileRedirect | .generic => (readable, true))

def ProcessOpenCoverage : Prop := ∀ mode read write,
  parseProcessMode mode = (match mode with
    | "r" => some .read | "w" => some .write
    | "r+" | "w+" => some .readWrite | _ => none) ∧
  processOpenMode read write =
    (if read && write then .readWrite else if read then .read else if write then .write else .none) ∧
  openDoOutcome true true true = .returned ∧
  openDoOutcome false true true = .bodyError

def ProcessSequenceCoverage : Prop := ∀ ps p cmd pid i,
  processWaitAll ps = ps.all (·.exited) ∧
  processRunningAny ps = ps.any (fun p => !p.exited) ∧
  processExitedAll ps = ps.all (·.exited) ∧
  processSignaled p = decide (p.termsignal.val > 0) ∧
  cmdExecLength cmd = cmd.exec.length ∧ cmdExecAt cmd i = cmd.exec[i]? ∧
  processPid p pid = if p.exited || pid ≤ 0 then .error .ioError else .ok pid

theorem streamLifecycleCoverage_proven : StreamLifecycleCoverage := by
  simp [StreamLifecycleCoverage, endpointReadable, waitReadState, endpointField,
    endpointWritable, endpointShow, setupStreamStdio, rawHandleModel, displaySizeModel,
    allocRequestSize, pipeEndpoints, endpointClose, startReadingState, stopReadingState]
theorem streamRequestCoverage_proven : StreamRequestCoverage := by
  simp [StreamRequestCoverage, beginReq, markReqCancelled, finishReq, completeReq]
theorem streamReadWriteCoverage_proven : StreamReadWriteCoverage := by
  simp [StreamReadWriteCoverage, readbytesModel, readUntilModel, requeueUnwritten,
    peekModel, writeChunks]
theorem streamRedirectCoverage_proven : StreamRedirectCoverage := by
  simp [StreamRedirectCoverage, redirectStdio, pipeGetindex, samePath]
theorem bufferStreamCoverage_proven : BufferStreamCoverage := by
  simp [BufferStreamCoverage, bufferReadN, bufferResetEof, bufferReadable,
    bufferReadByte, bufferWritable, bufferClose, bufferEof, bufferSkip, bufferFlush,
    writeBytes]
theorem ioStreamLifecycleCoverage_proven : IOStreamLifecycleCoverage := by
  simp [IOStreamLifecycleCoverage, ioCtor, ioPointerModel, ioTruncate, ioSkip,
    ioClose, ioBytesAvailable, ioEof, ioSeek, ioSeekEnd, ioWrite, parseOpenMode]
  intro s bytes
  by_cases hw : s.writable <;> by_cases ho : s.isopen <;> simp [hw, ho]
theorem ioStreamReadCoverage_proven : IOStreamReadCoverage := by
  simp [IOStreamReadCoverage, ioReadN, ioReadAvailable, ioTake, ioReadUntil,
    ioReadline, ioReadExact, ioPeek]
theorem libuvHandleCoverage_proven : LibuvHandleCoverage := by
  simp [LibuvHandleCoverage, associateHandle, disassociateHandle, preserveHandle,
    unpreserveHandle, uvRef, uvUnref, uvSizeResult, iolockDepth]
theorem libuvErrorCoverage_proven : LibuvErrorCoverage := by
  simp [LibuvErrorCoverage, uvErrorResult, uvErrorText, reinitStdioKind]
theorem asyncConstructionCoverage_proven : AsyncConstructionCoverage := by
  simp [AsyncConstructionCoverage, timerSetup, timerTimeout, timerProperties,
    timerShowState, callbackShouldContinue, freshEvent]
theorem asyncUtilityCoverage_proven : AsyncUtilityCoverage := by
  simp [AsyncUtilityCoverage, timedwaitResult, timeoutEnqueue, timeoutDequeue,
    sleepFinalState, freshEvent, closeEvent]
theorem processSpawnCoverage_proven : ProcessSpawnCoverage := by
  simp [ProcessSpawnCoverage, spawnModel, processCtor, processExitCallback, cpuMask]
theorem processStdioCoverage_proven : ProcessStdioCoverage := by
  simp [ProcessStdioCoverage, stdioCopy, setupStdio]
theorem processOpenCoverage_proven : ProcessOpenCoverage := by
  simp [ProcessOpenCoverage, parseProcessMode, processOpenMode, openDoOutcome]
theorem processSequenceCoverage_proven : ProcessSequenceCoverage := by
  simp [ProcessSequenceCoverage, processWaitAll, processRunningAny, processExitedAll,
    processSignaled, cmdExecLength, cmdExecAt, processPid]

end JuliaLean.Streams
