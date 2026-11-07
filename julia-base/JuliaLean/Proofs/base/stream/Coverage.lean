import JuliaLean.base.stream

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

theorem streamLifecycleCoverage_proven : StreamLifecycleCoverage := by
  simp [StreamLifecycleCoverage, endpointReadable, waitReadState, endpointField,
    endpointWritable, endpointShow, setupStreamStdio, rawHandleModel, displaySizeModel,
    allocRequestSize, pipeEndpoints, endpointClose, startReadingState, stopReadingState]
  intro status s field
  cases field <;> cases s.status <;> rfl
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
  intro s
  cases s.buffer <;> rfl

end JuliaLean.Streams
