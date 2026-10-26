import JuliaLean.Streams.Model

/-! Properties promised by Julia's stream and process documentation, or by
the state and FIFO invariants of the implementations. -/

namespace JuliaLean.Streams

/-- Bytes accepted by any modeled stream are returned in order: after closing
the writer of a connected libuv pair, directly for `BufferStream`, or after
rewinding an `IOStream`. -/
def WriteReadFIFO : Prop := ∀ kind bytes,
  (kind = .bufferStream ∨ kind = .ioStream) →
    (∃ written,
      writeBytes (freshStream kind) bytes = .ok (bytes.length, written) ∧
      readAvailable (closeStream written) =
        .ok (bytes, { closeStream written with buffer := [] })) ∧
    (∃ pipe,
      pipeWrite freshPipe bytes = .ok (bytes.length, pipe) ∧
      readAvailable (closePipeWrite pipe).readEnd =
        .ok (bytes, { (closePipeWrite pipe).readEnd with buffer := [] }))

/-- `unsafe_write` accepts exactly its length argument, and `unsafe_read`
returns exactly that many leading bytes when they are available. -/
def UnsafeLengthsExact : Prop :=
  (∀ kind memory n, n ≤ memory.length →
    ∃ written, unsafeWrite (freshStream kind) memory n = .ok (n, written)) ∧
  (∀ s n, n ≤ s.buffer.length →
    unsafeRead s n = .ok (s.buffer.take n, { s with buffer := s.buffer.drop n }))

/-- `readavailable` returns and consumes the complete buffered byte sequence. -/
def ReadAvailableExact : Prop := ∀ s,
  readAvailable s = .ok (s.buffer, { s with buffer := [] })

/-- The modeled first-delimiter split reconstructs the input, and
`readuntil`/`readline` return the documented bytes and consume through the
delimiter. -/
def DelimiterHandling : Prop := ∀ s delim keep,
  let r := splitUntil delim s.buffer
  r.before ++ (if r.found then delim :: r.after else []) = s.buffer ∧
  readUntil s delim keep =
    .ok (if r.found && keep then r.before ++ [delim] else r.before,
      { s with buffer := r.after }) ∧
  let line := splitUntil 10 s.buffer
  readLine s keep =
    .ok (if keep && line.found then line.before ++ [10]
         else if line.found then stripTrailingCR line.before else line.before,
      { s with buffer := line.after })

/-- A successful read operation cannot reopen a closed stream. -/
def ClosedReadsStayClosed : Prop := ∀ s n delim keep,
  s.status = .closed →
  (match unsafeRead s n with | .ok (_, s') => s'.status = .closed | .error _ => True) ∧
  (match readAvailable s with | .ok (_, s') => s'.status = .closed | .error _ => True) ∧
  (match readUntil s delim keep with | .ok (_, s') => s'.status = .closed | .error _ => True) ∧
  (match readLine s keep with | .ok (_, s') => s'.status = .closed | .error _ => True)

/-- Closing is idempotent, makes `isopen` false, and leaves EOF false exactly
while buffered data remains. -/
def CloseMonotone : Prop := ∀ s,
  closeStream (closeStream s) = closeStream s ∧
  isOpen (closeStream s) = false ∧
  streamEof (closeStream s) = s.buffer.isEmpty

/-- Closed libuv streams reject writes. -/
def ClosedLibuvWritesError : Prop := ∀ kind bytes,
  (kind = .libuvStream ∨ kind = .bufferStream) →
  ∃ err, writeBytes (closeStream (freshStream kind)) bytes = .error err

/-- A closed IOStream is not writable and a nonempty write raises an error. -/
def ClosedIOStreamWriteErrors : Prop := ∀ s bytes,
  s.kind = .ioStream → isOpen s = false → bytes ≠ [] →
  isWritable s = false ∧ ∃ err, writeBytes s bytes = .error err

/-- Closing a Timer or AsyncCondition is idempotent and later notifications
cannot reactivate it. A closed object without a pending event makes `wait`
throw EOFError. -/
def EventCloseIdempotent : Prop := ∀ e,
  closeEvent (closeEvent e) = closeEvent e ∧
  (closeEvent e).isopen = false ∧
  signalEvent (closeEvent e) = closeEvent e ∧
  (e.set = false → waitEvent (closeEvent e) = .error .eofError)

/-- Once a one-shot timer has fired, every subsequent wait returns immediately,
including after the timer has become inactive. -/
def OneShotWaitPersistent : Prop :=
  ∀ e, e.kind = .oneShotTimer → e.isopen = true → e.set = false →
    let fired := signalEvent e
    fired.isopen = false ∧ fired.set = true ∧
    waitEvent fired = .ok fired ∧
    (match waitEvent fired with | .ok after => waitEvent after = .ok after | .error _ => False)

/-- An event already set before close can be observed one final time, matching
the callback documentation. -/
def PendingEventSurvivesClose : Prop := ∀ kind,
  kind = .repeatingTimer ∨ kind = .asyncCondition →
  let pending := closeEvent (signalEvent (freshEvent kind))
  ∃ after, waitEvent pending = .ok after ∧ after.isopen = false

/-- Multi-stage pipelines associate from the left. -/
def PipelineLeftAssociative : Prop := ∀ a b c rest,
  pipelineMany a (b :: c :: rest) = pipelineMany (.stdoutPipe (.stdoutPipe a b) c) rest

/-- `ignorestatus(command)` accepts every command object. -/
def IgnoreStatusAllCommands : Prop := ∀ command,
  ∃ marked, ignoreStatus command = .ok marked

/-- `detach(::Cmd)` changes only the detached flag. -/
def DetachSetsFlag : Prop := ∀ cmd,
  (detachCmd cmd).flags = cmd.flags ||| detachedFlag ∧
  (detachCmd cmd).exec = cmd.exec ∧
  (detachCmd cmd).env = cmd.env ∧
  (detachCmd cmd).ignorestatus = cmd.ignorestatus

/-- `detach(command)` accepts every command object that `run` accepts. -/
def DetachAllCommands : Prop := ∀ command,
  ∃ detached, detachCommand command = .ok detached

/-- `success` is true exactly for an exited process with exit code zero and no
terminating signal; a positive signal is reported as that exact signal. -/
def ProcessStatusExact : Prop := ∀ p,
  (testSuccess p = true ↔
    p.exited = true ∧ p.exitcode.val = 0 ∧ p.termsignal.val = 0) ∧
  (p.exited = true → p.termsignal.val > 0 →
    processStatus p = .signaled p.termsignal.val)

/-- `ProcessFailedException` contains exactly the failed, non-ignored
processes, in pipeline order. -/
def ProcessFailureContents : Prop := ∀ ps,
  failedProcesses ps ≠ [] →
  pipelineError ps = .error (.processFailed ((failedProcesses ps).map (·.id)))

/-- `run` and `read(cmd)` use the same exit-status check, and a successful
read returns exactly the captured bytes. -/
def RunReadStatusHandling : Prop := ∀ ps output,
  (runResult ps = .ok () → readCommand output ps = .ok output) ∧
  (∀ err, runResult ps = .error err → readCommand output ps = .error err)

/-- `kill` is a no-op after exit; otherwise the exit callback reports the exact
positive signal and a zero exit code. -/
def KillReportsSignal : Prop := ∀ p signal,
  (p.exited = true → killProcess p signal = p) ∧
  (p.exited = false → signal.val > 0 →
    (killProcess p signal).exitcode.val = 0 ∧
    processStatus (killProcess p signal) = .signaled signal.val)

end JuliaLean.Streams
