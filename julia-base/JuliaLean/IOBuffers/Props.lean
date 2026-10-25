import JuliaLean.IOBuffers.Ops

/-!
Properties of `IOBuffer` (`base/iobuffer.jl`) stated over the model.

`Reachable io` holds for every buffer a program can obtain: a constructor call with
in-range arguments, followed by any sequence of operations (each with in-range
arguments). The total number of bytes the operations add stays below `2^60`, so
that the virtual position of a pipe (which counts every byte ever read) fits in an
`Int`; `copyline(out, s)` from a non-buffer stream is excluded because
`iobuffers-copyline-prior` refutes its contract.
-/

namespace JuliaLean.IOBuffers

open JuliaLean

instance instDecidableEqExceptIOErr {α} [DecidableEq α] : DecidableEq (Except IOErr α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (fun e => nomatch e)
  | .error _, .ok _ => isFalse (fun e => nomatch e)

/-- Value returned by `m` started in `io`. -/
def resultOf {α} (m : M α) (io : IOBuf) : Except IOErr α :=
  match m.run io with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-- State after `m` started in `io`, also when `m` throws. -/
def stateOf {α} (m : M α) (io : IOBuf) : IOBuf :=
  match m.run io with
  | .ok _ s => s
  | .error _ s => s

/-- The bytes of the buffer, `data[offset+1:size]`: everything `seekstart(io); read(io)`
returns for a seekable buffer. -/
def content (io : IOBuf) : List UInt8 := slice io.data ((getOffset io).val + 1) io.size.val

/-- The bytes available for reading, `data[ptr:size]`. -/
def avail (io : IOBuf) : List UInt8 := slice io.data io.ptr.val io.size.val

/-- Size limit on what one program feeds a buffer. -/
def bound : Nat := 2 ^ 60

/-- A value of type `Int`. -/
abbrev isInt (x : Int) : Prop := -2 ^ 63 ≤ x ∧ x < 2 ^ 63

def DataArg.ok : DataArg → Prop
  | .vec v => v.off + v.len ≤ v.mem.length ∧ v.mem.length ≤ bound
  | .mem d => d.length ≤ bound
  | .other d => d.length ≤ bound

/-- In-range constructor arguments. -/
def Ctor.ok : Ctor → Prop
  | .empty _ _ _ _ m s => 0 ≤ m ∧ m < 2 ^ 63 ∧ (∀ h, s = some h → isInt h ∧ h ≤ bound)
  | .data d _ _ _ _ m => d.ok ∧ 0 ≤ m ∧ m < 2 ^ 63
  | .str s => s.length ≤ bound
  | .pipe d m => d.ok ∧ 0 ≤ m ∧ m < 2 ^ 63
  | .pipeN m => 0 ≤ m ∧ m ≤ bound

/-- In-range operation arguments; `copyline` from a non-buffer stream is excluded. -/
def Op.ok : Op → Prop
  | .writeBytes bs => bs.length ≤ bound
  | .readN n => isInt n
  | .readBang n => n ≤ bound
  | .readbytes n => isInt n
  | .truncate n => isInt n
  | .copyline _ _ => False
  | _ => True

/-- Bytes an operation may add to a buffer. -/
def Op.weight : Op → Nat
  | .writeByte _ => 1
  | .writeBytes bs => bs.length
  | .truncate n => n.toNat
  | _ => 0

/-- A buffer obtainable by a program. -/
def Reachable (io : IOBuf) : Prop :=
  ∃ (c : Ctor) (ops : List Op) (io0 : IOBuf), c.ok ∧ c.build = .ok io0 ∧ (∀ o ∈ ops, Op.ok o) ∧
    (ops.map Op.weight).sum ≤ bound ∧ io = finalState ops io0

/-- `position`, `bytesavailable`, `eof`, `filesize` and `maxsize` agree. -/
def Consistent (io : IOBuf) : Prop :=
  0 ≤ (bytesavailable io).val ∧ (eof io = true ↔ (bytesavailable io).val = 0) ∧
  0 ≤ (position io).val ∧
  (io.seekable = true → (position io).val + (bytesavailable io).val = (filesize io).val) ∧
  (avail io).length = (bytesavailable io).val ∧
  (io.size - getOffset io).val ≤ io.maxsize.val

/-- After any sequence of operations, `position`, `bytesavailable` and `eof` are
consistent, and the buffer never stores more than `maxsize` bytes. -/
def InvariantHolds : Prop := ∀ io, Reachable io → Consistent io

/-- No operation on a reachable buffer accesses memory outside `data`. -/
def NoOutOfBounds : Prop :=
  ∀ io, Reachable io → ∀ o, Op.ok o → resultOf (runOp o) io ≠ .error .outOfBounds

/-- `io = IOBuffer(maxsize=m)`; `write(io, w)` for each `w`; `seekstart(io)`;
`read(io)` returns the first `m` bytes written. -/
def WriteReadRoundtrip : Prop :=
  ∀ (m : Int) (ws : List (List UInt8)), 0 ≤ m → m < 2 ^ 63 → (ws.map List.length).sum ≤ bound →
    ∃ io, iobufferEmpty (some true) (some true) none (some true) m none = .ok io ∧
      resultOf readAll (finalState (ws.map Op.writeBytes ++ [Op.seekstart]) io) =
        .ok (ws.flatten.take m.toNat)

/-- `write(io, w)` on a seekable, writable, non-append `IOBuffer` overwrites from the
current position and extends the buffer as needed; it writes `min(length(w), maxsize -
position(io))` bytes and advances the position by that much. -/
def WriteAtPosition : Prop :=
  ∀ io, Reachable io → io.isMem = true → io.writable = true → io.seekable = true →
    io.append = false → ∀ w : List UInt8, w.length ≤ bound →
      let k := min w.length (io.maxsize.val - (position io).val).toNat
      resultOf (unsafeWrite w) io = .ok (i k) ∧
      content (stateOf (unsafeWrite w) io) =
        (content io).take (position io).val.toNat ++ w.take k ++ (content io).drop ((position io).val.toNat + k) ∧
      (position (stateOf (unsafeWrite w) io)).val = (position io).val + k

/-- Bytes retained by an append buffer: all of them if it is seekable, else the bytes
from the mark (or from the read position if unmarked) to the end. -/
def heldBytes (io : IOBuf) : Int :=
  if io.seekable then (filesize io).val
  else if ismarked io then (position io).val - io.mark.val + (bytesavailable io).val
  else (bytesavailable io).val

/-- `write(io, w)` on a writable append buffer (`append=true` or a `PipeBuffer`) adds
`min(length(w), maxsize - held)` bytes at the end, where `held` is the number of bytes
the buffer must keep, and leaves the read position alone. -/
def AppendWritesAtEnd : Prop :=
  ∀ io, Reachable io → io.isMem = true → io.writable = true → io.append = true →
    ∀ w : List UInt8, w.length ≤ bound →
      let k := min w.length (io.maxsize.val - heldBytes io).toNat
      resultOf (unsafeWrite w) io = .ok (i k) ∧
      avail (stateOf (unsafeWrite w) io) = avail io ++ w.take k ∧
      position (stateOf (unsafeWrite w) io) = position io

/-- Operations of a pipe client: writes and reads. -/
def Op.isPipeIO : Op → Prop
  | .writeByte _ => True
  | .writeBytes bs => bs.length ≤ bound
  | .readByte => True
  | .readN n => 0 ≤ n ∧ n < 2 ^ 63
  | .readAll => True
  | _ => False

/-- Bytes written by an operation. -/
def Op.written : Op → List UInt8
  | .writeByte b => [b]
  | .writeBytes bs => bs
  | _ => []

/-- Bytes returned by a step. -/
def readOut : Except IOErr Val → List UInt8
  | .ok (.bytes bs) => bs
  | _ => []

/-- `PipeBuffer()`: after any interleaving of writes and reads, the bytes read so far
followed by the bytes still available are exactly the bytes written, in order. -/
def PipeFIFO : Prop :=
  ∀ ops : List Op, (∀ o ∈ ops, Op.isPipeIO o) → (ops.map Op.weight).sum ≤ bound →
    ∃ io0, pipeBuffer = .ok io0 ∧
      ((runOps ops io0).map (fun s => readOut s.1)).flatten ++ avail (finalState ops io0) =
        (ops.map Op.written).flatten

/-- `PipeBuffer()` holding `w0`: `mark`, then any writes and reads (which may compact
the buffer), then `reset` returns the marked position, and the bytes available again
are `w0` followed by everything written after the mark. -/
def PipeMarkReset : Prop :=
  ∀ (w0 : List UInt8) (ops : List Op), w0.length ≤ bound → (∀ o ∈ ops, Op.isPipeIO o) →
    (ops.map Op.weight).sum ≤ bound →
    ∃ io0, pipeBuffer = .ok io0 ∧
      let io1 := finalState [Op.writeBytes w0, Op.mark] io0
      let io2 := finalState ops io1
      resultOf reset io2 = .ok (position io1) ∧
      avail (stateOf reset io2) = w0 ++ (ops.map Op.written).flatten

/-- `seek(io, n)` on a seekable buffer moves to `clamp(n, 0, filesize(io))`; on a
pipe it succeeds only for `n == mark` and then moves to the mark. -/
def SeekSpec : Prop :=
  ∀ io, Reachable io → ∀ n : Int,
    (io.seekable = true → resultOf (seekAny n) io = .ok () ∧
      (position (stateOf (seekAny n) io)).val = max 0 (min n (filesize io).val)) ∧
    (io.seekable = false →
      ((∃ e, resultOf (seekAny n) io = .error e) ↔ ¬ (ismarked io = true ∧ n = io.mark.val)) ∧
      (ismarked io = true → n = io.mark.val → (position (stateOf (seekAny n) io)).val = n))

/-- `skip(io, n)` for `n ≥ 0` advances by `min(n, bytesavailable(io))`; for `n < 0` on a
seekable buffer it moves back to `max(0, position + n)`. -/
def SkipSpec : Prop :=
  ∀ io, Reachable io → ∀ n : Int,
    (0 ≤ n → resultOf (skip n) io = .ok () ∧
      (position (stateOf (skip n) io)).val = (position io).val + min n (bytesavailable io).val) ∧
    (n < 0 → io.seekable = true → resultOf (skip n) io = .ok () ∧
      (position (stateOf (skip n) io)).val = max 0 ((position io).val + n))

/-- `truncate(io, n)` throws an `ArgumentError` exactly when the buffer is not writable or
not seekable, `n < 0`, or `n > maxsize`; otherwise the buffer holds exactly `n` bytes:
its old bytes, cut or padded with zeros, and the position is at most `n`. The model has no
`OutOfMemoryError`, so the size claim is stated for `n ≤ 2^60` (Julia cannot allocate more). -/
def TruncateSpec : Prop :=
  ∀ io, Reachable io → io.isMem = true → ∀ n : Int, isInt n →
    ((∃ msg, resultOf (truncate (i n)) io = .error (.jl (.argumentError msg))) ↔
      (io.writable = false ∨ io.seekable = false ∨ n < 0 ∨ n > io.maxsize.val)) ∧
    (n ≤ bound → resultOf (truncate (i n)) io = .ok () →
      content (stateOf (truncate (i n)) io) = (content io ++ List.replicate n.toNat 0).take n.toNat ∧
      (position (stateOf (truncate (i n)) io)).val = min (position io).val n)

/-- `truncate(io, n)` keeps a mark at a position `≤ n`, which is still inside the buffer. -/
def TruncateKeepsMark : Prop :=
  ∀ io, Reachable io → io.isMem = true → ∀ n : Int, isInt n → ismarked io = true →
    io.mark.val ≤ n → resultOf (truncate (i n)) io = .ok () →
    ismarked (stateOf (truncate (i n)) io) = true

/-- `take!(io)` on a writable `IOBuffer` returns its bytes (the unread bytes of a pipe) and
empties it: afterwards `position`, `bytesavailable` and `filesize` are zero and it is
unmarked. -/
def TakeSpec : Prop :=
  ∀ io, Reachable io → io.isMem = true → io.writable = true →
    resultOf take io = .ok (if io.seekable then content io else avail io) ∧
    (position (stateOf take io)).val = 0 ∧ (bytesavailable (stateOf take io)).val = 0 ∧
    (filesize (stateOf take io)).val = 0 ∧ ismarked (stateOf take io) = false

/-- `take!(io)` on a readable `IOBuffer` that is not writable returns its bytes (the
unread bytes of a pipe) instead of throwing. -/
def TakeReadOnly : Prop :=
  ∀ io, Reachable io → io.isMem = true → io.readable = true → io.writable = false →
    resultOf take io = .ok (if io.seekable then content io else avail io)

/-- After `take!(io)` the buffer is "reset to its initial state": its position is 0. -/
def TakeResets : Prop :=
  ∀ io, Reachable io → io.isMem = true → io.readable = true →
    (∃ bs, resultOf take io = .ok bs) → (position (stateOf take io)).val = 0

/-- `takestring!(io)` returns the same bytes as `String(take!(io))`. -/
def TakestringEqTake : Prop :=
  ∀ io, Reachable io → io.isMem = true → ∀ bs, resultOf take io = .ok bs →
    resultOf takestring io = .ok bs

/-- Reads from a readable buffer: `read(io, n)` returns the next `min(n, bytesavailable)`
bytes, `readbytes!` returns the same count and bytes, `read(io, UInt8)` the next byte or
`EOFError`, and `peek` leaves the buffer unchanged. -/
def ReadSpec : Prop :=
  ∀ io, Reachable io → io.readable = true →
    (∀ n : Int, 0 ≤ n → n < 2 ^ 63 →
      resultOf (readN (i n)) io = .ok ((avail io).take n.toNat) ∧
      avail (stateOf (readN (i n)) io) = (avail io).drop n.toNat ∧
      (position (stateOf (readN (i n)) io)).val = (position io).val + min n (bytesavailable io).val ∧
      resultOf (readbytes (i n)) io = .ok (i (min n (bytesavailable io).val), (avail io).take n.toNat)) ∧
    (avail io = [] → resultOf readByte io = .error .eofError ∧ resultOf peekByte io = .error .eofError) ∧
    (∀ b rest, avail io = b :: rest → resultOf readByte io = .ok b ∧ avail (stateOf readByte io) = rest ∧
      resultOf peekByte io = .ok b ∧ stateOf peekByte io = io)

/-- Bytes `readuntil(io, d; keep)` returns. -/
def untilSpec (a : List UInt8) (d : UInt8) (keep : Bool) : List UInt8 :=
  match a.idxOf? d with
  | some k => if keep then a.take (k + 1) else a.take k
  | none => a

/-- Bytes `readline(io; keep)` returns: the line, without `\n` or `\r\n` unless `keep`. -/
def lineSpec (a : List UInt8) (keep : Bool) : List UInt8 :=
  match a.idxOf? 0x0a with
  | some k => if keep then a.take (k + 1)
              else if 0 < k ∧ a.getD (k - 1) 0 = 0x0d then a.take (k - 1) else a.take k
  | none => a

/-- Bytes left after reading through the first `d`. -/
def afterSpec (a : List UInt8) (d : UInt8) : List UInt8 :=
  match a.idxOf? d with
  | some k => a.drop (k + 1)
  | none => []

/-- `readuntil` and `readline` on a readable buffer return the bytes up to the delimiter
(with or without it, per `keep`) and consume them with the delimiter. -/
def ReadUntilSpec : Prop :=
  ∀ io, Reachable io → io.readable = true → ∀ (d : UInt8) (keep : Bool),
    resultOf (readuntil d keep) io = .ok (untilSpec (avail io) d keep) ∧
    avail (stateOf (readuntil d keep) io) = afterSpec (avail io) d ∧
    resultOf (readline keep) io = .ok (lineSpec (avail io) keep) ∧
    avail (stateOf (readline keep) io) = afterSpec (avail io) 0x0a

/-- `readuntil(io, d)` and `readline(io)` on a buffer that is not readable throw the
`ArgumentError` that `read` throws. -/
def ReadUntilUnreadable : Prop :=
  ∀ io, Reachable io → io.readable = false → ∀ (d : UInt8) (keep : Bool),
    (∃ msg, resultOf (readuntil d keep) io = .error (.jl (.argumentError msg))) ∧
    (∃ msg, resultOf (readline keep) io = .error (.jl (.argumentError msg)))

/-- `occursin(d, io)` tells whether `d` is among the bytes available. -/
def OccursinSpec : Prop :=
  ∀ io, Reachable io → ∀ d : UInt8, occursin d io = .ok (decide (d ∈ avail io))

/-- `peek(io, Int8)` leaves the buffer's mark alone. -/
def PeekKeepsMark : Prop :=
  ∀ io, Reachable io → io.readable = true → avail io ≠ [] →
    (stateOf peekGeneric io).mark = io.mark

/-- What `copyline` with `keep=false` writes: the line without its `\n` or `\r\n`. -/
def stripNewline (l : List UInt8) : List UInt8 :=
  if l.getLast? = some 0x0a then
    if l.dropLast.getLast? = some 0x0d then l.dropLast.dropLast else l.dropLast
  else l

/-- The observable state of a buffer. -/
def observe (io : IOBuf) : List UInt8 × Int × List UInt8 :=
  (content io, (position io).val, avail io)

/-- A line from a stream: no newline except possibly at the end. -/
abbrev isLine (l : List UInt8) : Prop := 0x0a ∉ l.dropLast

/-- `copyline(out, s)` from a stream that is not a buffer, with `keep=false`, into the
middle of `out`: same effect as writing the stripped line. -/
def CopylineMiddle : Prop :=
  ∀ out, Reachable out → out.isMem = true → out.writable = true → out.append = false →
    out.ptr.val ≤ out.size.val → out.maxsize.val = 2 ^ 63 - 1 → ∀ l, isLine l → l.length ≤ bound →
      observe (stateOf (copylineFrom l false) out) = observe (stateOf (unsafeWrite (stripNewline l)) out)

/-- `copyline(out, s)` from a stream that is not a buffer, with `keep=false`, at the end
of `out`: same effect as writing the stripped line, so the bytes already in `out` are
untouched. -/
def CopylineAtEnd : Prop :=
  ∀ out, Reachable out → out.isMem = true → out.writable = true →
    (out.append = true ∨ out.ptr.val = out.size.val + 1) → out.maxsize.val = 2 ^ 63 - 1 →
    ∀ l, isLine l → l.length ≤ bound →
      observe (stateOf (copylineFrom l false) out) = observe (stateOf (unsafeWrite (stripNewline l)) out)

/-- Writing to a writable buffer over any vector type stores the bytes (up to `maxsize`)
instead of throwing a `MethodError`. -/
def WriteNoMethodError : Prop :=
  ∀ io, Reachable io → io.writable = true → ∀ w : List UInt8, w.length ≤ bound →
    ∀ fn, resultOf (unsafeWrite w) io ≠ .error (.jl (.methodError fn))

/-- `PipeBuffer(data; maxsize)` accepts `maxsize` of any integer type, as documented
(`maxsize::Integer`). -/
def PipeBufferMaxsizeInteger : Prop :=
  ∀ (t : IntTy) (m : Int), t.min ≤ m → m ≤ t.max → 0 ≤ m → m < 2 ^ 63 →
    ∃ io, pipeBuffer (.mem []) t m = .ok io

end JuliaLean.IOBuffers
