import JuliaLean.base.stream

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





end JuliaLean.Streams
