import JuliaLean.base.iobuffer
import JuliaLean.Registry.Types

/-!
Properties for `base/iobuffer.jl` stated over the source-mirrored `BufferState` model.
Every buffer premise is the field invariant; each registry entry remains open for proof or
refutation in the next phase.
-/

namespace JuliaLean.Proofs.base.iobuffer

open JuliaLean JuliaLean.Registry JuliaLean.base.iobuffer

instance instDecidableEqExceptIOErr {α} [DecidableEq α] : DecidableEq (Except IOErr α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (fun e => nomatch e)
  | .error _, .ok _ => isFalse (fun e => nomatch e)

def resultOf {α} (m : M α) (io : BufferState) : Except IOErr α :=
  match m.run io with
  | .ok a _ => .ok a
  | .error e _ => .error e

def stateOf {α} (m : M α) (io : BufferState) : BufferState :=
  match m.run io with
  | .ok _ s => s
  | .error _ s => s

def content (io : BufferState) : List UInt8 :=
  slice io.data ((getOffset io).val + 1) io.size.val

def available (io : BufferState) : List UInt8 := slice io.data io.ptr.val io.size.val

def positionWithin (io : BufferState) : Prop :=
  0 ≤ (source_position io).val ∧ (source_position io).val ≤ (logicalSize io).val

def observe (io : BufferState) : List UInt8 × Int × List UInt8 :=
  (content io, (source_position io).val, available io)

/-- The list models a Julia `Vector{UInt8}`, whose length is a nonnegative `Int`. -/
def vectorBytesValid (bytes : List UInt8) : Prop := bytes.length < 2 ^ 63

def writeThenRead (bytes : List UInt8) : M (List UInt8) := do
  let _ ← writeBytesModel bytes
  source_seek (i 0)
  readAllModel


def untilSpec (bytes : List UInt8) (delimiter : UInt8) (keep : Bool) : List UInt8 :=
  match bytes.idxOf? delimiter with
  | some k => bytes.take (if keep then k + 1 else k)
  | none => bytes

def afterSpec (bytes : List UInt8) (delimiter : UInt8) : List UInt8 :=
  match bytes.idxOf? delimiter with
  | some k => bytes.drop (k + 1)
  | none => []

def lineSpec (bytes : List UInt8) (keep : Bool) : List UInt8 :=
  match bytes.idxOf? 0x0a with
  | some k =>
      if keep then bytes.take (k + 1)
      else if 0 < k && bytes[k - 1]! = 0x0d then bytes.take (k - 1)
      else bytes.take k
  | none => bytes

def stripNewline (line : List UInt8) : List UInt8 :=
  if line.getLast? = some 0x0a then
    if line.dropLast.getLast? = some 0x0d then line.dropLast.dropLast else line.dropLast
  else line
def writeBytesState (io : BufferState) (bytes : List UInt8) : Except IOErr BufferState :=
  match (writeBytesModel bytes).run io with
  | .ok _ next => .ok next
  | .error error _ => .error error

def writeBytesCancelModel (out : BufferState) (bytes : List UInt8) (_cancel : Unit) :
    Except IOErr BufferState :=
  writeBytesState out bytes

def copyUntilLineModel (out : BufferState) (stream : List UInt8) (delimiter : UInt8)
    (keep : Bool) : Except IOErr BufferState := do
  let input := source_new_generic_iobuffer stream id (fun _ => true)
    true false true false imaxval
  let (next, _) ← source_copyuntil writeBytesState writeBytesCancelModel () ()
    out input delimiter keep
  pure next

def copyUntilLineTokenModel (out : BufferState) (stream : List UInt8) (delimiter : UInt8)
    (keep : Bool) (_cancel : Unit) : Except IOErr BufferState :=
  copyUntilLineModel out stream delimiter keep

inductive PipeAction where
  | writeBytes (bytes : List UInt8)
  | readBytes (count : Int)
  deriving DecidableEq

def runPipeActionsWithWrites : List PipeAction → M (List UInt8 × List UInt8)
  | [] => pure ([], [])
  | .writeBytes bytes :: actions => do
      let count ← writeBytesModel bytes
      let (observed, writes) ← runPipeActionsWithWrites actions
      pure (observed, bytes.take count.val.toNat ++ writes)
  | .readBytes count :: actions => do
      let bytes ← source_read_n (fun count => readBang count) count
      let (observed, writes) ← runPipeActionsWithWrites actions
      pure (bytes ++ observed, writes)

def pipeActionsValid : List PipeAction → Prop
  | [] => True
  | .writeBytes bytes :: actions => vectorBytesValid bytes ∧ pipeActionsValid actions
  | .readBytes count :: actions => 0 ≤ count ∧ pipeActionsValid actions


/-! ## Core buffer contracts -/

/-- Position/file-size identities hold and successful operations preserve the field invariant. -/
def InvariantHolds : Prop :=
  ∀ io, stateInvariant io →
    positionWithin io ∧ 0 ≤ (source_bytesavailable io).val ∧
    (source_eof io = true ↔ (source_bytesavailable io).val = 0) ∧
    (io.seekable = true →
      (source_position io).val + (source_bytesavailable io).val = (source_filesize io).val) ∧
    (∀ bytes, vectorBytesValid bytes → ∀ n : Int,
      (∀ count, resultOf (writeBytesModel bytes) io = .ok count →
        stateInvariant (stateOf (writeBytesModel bytes) io)) ∧
      (resultOf (ensureRoomModel (u bytes.length)) io = .ok () →
        stateInvariant (stateOf (ensureRoomModel (u bytes.length)) io)) ∧
      (∀ byte, resultOf source_read_uint8 io = .ok byte →
        stateInvariant (stateOf source_read_uint8 io)) ∧
      (resultOf (source_seek (clampToI n)) io = .ok () →
        stateInvariant (stateOf (source_seek (clampToI n)) io)) ∧
      (resultOf (source_skip source_seek (clampToI n)) io = .ok () →
        stateInvariant (stateOf (source_skip source_seek (clampToI n)) io)) ∧
      (resultOf (source_truncate n) io = .ok () →
        stateInvariant (stateOf (source_truncate n) io)) ∧
      (∀ count, resultOf source_compact io = .ok count →
        stateInvariant (stateOf source_compact io)) ∧
      (resultOf source_closewrite io = .ok () →
        stateInvariant (stateOf source_closewrite io)) ∧
      (∀ taken, resultOf (source_take_generic (fun count => readBang count)) io = .ok taken →
        stateInvariant (stateOf (source_take_generic (fun count => readBang count)) io)) ∧
      (∀ taken, resultOf (source_take_IOBuffer wrapBytes) io = .ok taken →
        stateInvariant (stateOf (source_take_IOBuffer wrapBytes) io)) ∧
      (resultOf (source_close (fun size exact => resize size exact)) io = .ok () →
        stateInvariant (stateOf (source_close (fun size exact => resize size exact)) io)))

/-- Checked reads, writes, compaction, resizing, and unsafe reads stay inside backing bytes. -/
def NoOutOfBounds : Prop :=
  ∀ io, stateInvariant io → ∀ bytes, vectorBytesValid bytes →
    resultOf (writeBytesModel bytes) io ≠ .error .outOfBounds ∧
    resultOf source_read_uint8 io ≠ .error .outOfBounds ∧
    resultOf source_peek_uint8 io ≠ .error .outOfBounds ∧
    (∀ n : U,
      resultOf (source_unsafe_read
        (fun (_ : Unit) data ptr count => do
          let _ ← readAt data ptr count.val.toNat
          pure ()) () n) io ≠ .error .outOfBounds) ∧
    resultOf source_compact io ≠ .error .outOfBounds ∧
    resultOf (source_resize false (fun data n => .ok (data.take n.val.toNat))
      (fun _ n => .ok (List.replicate n.val.toNat 0)) false (i bytes.length)) io ≠
      .error .outOfBounds

/-- A seekable non-append write overwrites from the current position and advances by the
number of bytes that fit before `maxsize`. -/
def WriteAtPosition : Prop :=
  ∀ io, stateInvariant io → io.writable = true → io.seekable = true → io.append = false →
    ∀ bytes, vectorBytesValid bytes →
      let ensureRoom := ensureRoomModel
      let write := source_unsafe_write (fun _ => .ok ()) ensureRoom writePointerModel
        () bytes (u bytes.length)
      let room := stateOf (ensureRoom (u bytes.length)) io
      let start := room.ptr - i 1
      let k := min bytes.length (max 0 (room.maxsize.val - (source_position room).val)).toNat
      resultOf (ensureRoom (u bytes.length)) io = .ok () ∧
      stateInvariant room ∧
      resultOf write io = .ok (i k) ∧
      (stateOf write io).data =
        room.data.take start.val.toNat ++ bytes.take k ++ room.data.drop (start.val.toNat + k) ∧
      (source_position (stateOf write io)).val =
        (source_position io).val + (i k).val

/-- Append writes add bytes at the end, stop at `maxsize`, and leave the read position alone. -/
def AppendWritesAtEnd : Prop :=
  ∀ io, stateInvariant io → io.writable = true → io.append = true →
    ∀ bytes, vectorBytesValid bytes →
      let ensureRoom := ensureRoomModel
      let write := source_unsafe_write (fun _ => .ok ()) ensureRoom writePointerModel
        () bytes (u bytes.length)
      let room := stateOf (ensureRoom (u bytes.length)) io
      let start := room.size
      let k := min bytes.length
        (max 0 (room.maxsize.val - (room.size - getOffset room).val)).toNat
      let next := stateOf write io
      resultOf (ensureRoom (u bytes.length)) io = .ok () ∧
      stateInvariant room ∧
      resultOf write io = .ok (i k) ∧
      next.data =
        room.data.take start.val.toNat ++ bytes.take k ++ room.data.drop (start.val.toNat + k) ∧
      available room = available io ∧
      available next = available room ++ bytes.take k ∧
      (source_position next).val = (source_position io).val

/-- Writing bytes, seeking to zero, and reading returns the first `maxsize` bytes. -/
def WriteReadRoundtrip : Prop :=
  ∀ io, stateInvariant io → io.readable = true → io.writable = true → io.seekable = true →
    io.append = false → io.size = io.offset → io.ptr = io.offset + i 1 →
    ∀ bytes, vectorBytesValid bytes →
      resultOf (writeThenRead bytes) io = .ok (bytes.take io.maxsize.val.toNat)

/-- Every interleaving of pipe writes and reads preserves the order of written bytes. -/
def PipeFIFO : Prop :=
  ∀ io, stateInvariant io → io.seekable = false → io.readable = true →
    io.writable = true → io.append = true → ∀ actions,
      pipeActionsValid actions →
      ∃ observed writes, resultOf (runPipeActionsWithWrites actions) io = .ok (observed, writes) ∧
        observed ++ available (stateOf (runPipeActionsWithWrites actions) io) = available io ++ writes

/-- Pipe reset restores the position saved by the `base/io.jl` mark/reset methods. -/
def PipeMarkReset : Prop :=
  ∀ (markMethod resetMethod : M I),
    (∀ io, stateInvariant io →
      resultOf markMethod io = .ok (source_position io) ∧
      (stateOf markMethod io).mark = source_position io) →
    (∀ io, stateInvariant io → ismarked io = true →
      resultOf resetMethod io = .ok io.mark ∧
      source_position (stateOf resetMethod io) = io.mark) →
    ∀ io, stateInvariant io → io.seekable = false → io.readable = true →
      io.writable = true → io.append = true → ∀ before actions,
        vectorBytesValid before → pipeActionsValid actions →
        let markAction : M I := do
          let count ← writeBytesModel before
          let _ ← markMethod
          pure count
        ∃ beforeCount,
          resultOf markAction io = .ok beforeCount ∧
          let marked := stateOf markAction io
          let afterActions := stateOf (runPipeActionsWithWrites actions) marked
          ∃ observed writes,
            resultOf (runPipeActionsWithWrites actions) marked = .ok (observed, writes) ∧
            resultOf resetMethod afterActions = .ok marked.mark ∧
            available (stateOf resetMethod afterActions) =
              available io ++ before.take beforeCount.val.toNat ++ writes
/-- Seeking clamps seekable positions and rejects non-seekable positions other than the mark. -/
def SeekSpec : Prop :=
  ∀ io, stateInvariant io → ∀ n : Int,
    (io.seekable = true →
      resultOf (source_seek_integer (fun _ p => source_seek p) io n) io = .ok () ∧
      (source_position (stateOf (source_seek (clampToI n)) io)).val =
        max 0 (min n (source_filesize io).val)) ∧
    (io.seekable = false →
      (resultOf (source_seek (clampToI n)) io =
        if ismarked io then
          if clampToI n = io.mark then .ok ()
          else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked"))) ∧
      (ismarked io = true → clampToI n = io.mark →
        (source_position (stateOf (source_seek (clampToI n)) io)).val = io.mark.val))

/-- Positive skip stops at the end; negative skip moves backward only when seeking permits it. -/
def SkipSpec : Prop :=
  ∀ io, stateInvariant io → ∀ n : Int,
    (0 ≤ n → resultOf (source_skip_integer (fun _ p => source_skip source_seek p) io n) io = .ok () ∧
      (source_position (stateOf (source_skip source_seek (clampToI n)) io)).val =
        (source_position io).val + min n (source_bytesavailable io).val) ∧
    (n < 0 → io.seekable = true → resultOf (source_skip source_seek (clampToI n)) io = .ok () ∧
      (source_position (stateOf (source_skip source_seek (clampToI n)) io)).val =
        max 0 ((source_position io).val + n)) ∧
    (n < 0 → io.seekable = false →
      let target := clampToI ((source_position io).val + (clampToI n).val)
      resultOf (source_skip source_seek (clampToI n)) io =
        if ismarked io then
          if target = io.mark then .ok ()
          else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
        else .error (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked")))

/-- Truncation checks writability, seekability, nonnegative length and `maxsize`, then
retains or zero-pads bytes and clamps position to the new end. -/
def TruncateSpec : Prop :=
  ∀ io, stateInvariant io → ∀ n : Int,
    (resultOf (source_truncate n) io =
      if io.writable = false then
        .error (.jl (.argumentError "truncate failed, IOBuffer is not writeable"))
      else if io.seekable = false then
        .error (.jl (.argumentError "truncate failed, IOBuffer is not seekable"))
      else if n < 0 then
        .error (.jl (.argumentError ("truncate failed, n bytes must be ≥ 0, got " ++ toString n)))
      else if n > io.maxsize.val then
        .error (.jl (.argumentError
          ("truncate failed, n bytes is exceeds IOBuffer maxsize " ++ toString io.maxsize.val)))
      else .ok ()) ∧
    (0 ≤ n → n ≤ io.maxsize.val → resultOf (source_truncate n) io = .ok () →
      content (stateOf (source_truncate n) io) =
        (content io ++ List.replicate n.toNat 0).take n.toNat ∧
      (source_position (stateOf (source_truncate n) io)).val = min (source_position io).val n)

/-- A writable `take!` returns retained contents and resets position, size, and mark. -/
def TakeSpec : Prop :=
  ∀ io, stateInvariant io → io.isMemory = true → io.writable = true →
    resultOf (source_take_IOBuffer wrapBytes) io =
      .ok (if io.seekable then content io else available io) ∧
    (source_position (stateOf (source_take_IOBuffer wrapBytes) io)).val = 0 ∧
    (source_bytesavailable (stateOf (source_take_IOBuffer wrapBytes) io)).val = 0 ∧
    (source_filesize (stateOf (source_take_IOBuffer wrapBytes) io)).val = 0 ∧
    ismarked (stateOf (source_take_IOBuffer wrapBytes) io) = false

def readbytesResizeModel (bytes : List UInt8) (n : Int) : Except IOErr (List UInt8) :=
  .ok (bytes ++ List.replicate (n - bytes.length).toNat 0)

def readbytesBoundsModel (bytes : List UInt8) (n : I) : Except IOErr Unit :=
  if 0 ≤ n.val ∧ n.val ≤ bytes.length then .ok () else .error (.jl .boundsError)

def readbytesAdvanceModel (_io : BufferState) (_pointer : Unit) (n : U) : M Unit :=
  modify fun io => { io with ptr := io.ptr + i n.val }

/-- Counted reads return the unread prefix; `readbytes!` stores it in the destination, and `peek` leaves position unchanged. -/
def ReadSpec : Prop :=
  ∀ io, stateInvariant io → io.readable = true →
    (∀ n : Int, 0 ≤ n →
      resultOf (source_read_n (fun count => readBang count) n) io =
        .ok ((available io).take n.toNat) ∧
      available (stateOf (source_read_n (fun count => readBang count) n) io) =
        (available io).drop n.toNat ∧
      (source_position (stateOf (source_read_n (fun count => readBang count) n) io)).val =
        (source_position io).val + min n (source_bytesavailable io).val) ∧
    (available io = [] → resultOf source_read_uint8 io = .error .eofError ∧
      resultOf source_peek_uint8 io = .error .eofError) ∧
    (∀ byte rest, available io = byte :: rest →
      resultOf source_read_uint8 io = .ok byte ∧
      available (stateOf source_read_uint8 io) = rest ∧
      resultOf source_peek_uint8 io = .ok byte ∧ stateOf source_peek_uint8 io = io) ∧
    (∀ b, b.length < 2 ^ 63 →
      let count := imin (i b.length) (source_bytesavailable io)
      resultOf (source_readbytes_default (fun bytes => bytes.length) id toI
        readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b none) io =
        .ok count ∧
      available (stateOf
        (source_readbytes_default (fun bytes => bytes.length) id toI
          readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b none) io) =
        (available io).drop count.val.toNat ∧
      (source_position (stateOf
        (source_readbytes_default (fun bytes => bytes.length) id toI
          readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b none) io)).val =
        (source_position io).val + count.val) ∧
    (∀ {N : Type} (convertInt : N → Except IOErr I) (b : List UInt8) (nb : N) error,
      convertInt nb = .error error →
      resultOf (source_readbytes_default (fun bytes => bytes.length) (fun _ => nb) convertInt
        readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b (some nb)) io =
        .error error) ∧
    (∀ b n, b.length < 2 ^ 63 → 0 ≤ n → n < 2 ^ 63 →
      let count := imin (i n) (source_bytesavailable io)
      resultOf (source_readbytes_int (fun bytes => bytes.length)
        readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b (i n)) io =
        .ok count ∧
      available (stateOf
        (source_readbytes_int (fun bytes => bytes.length)
          readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b (i n)) io) =
        (available io).drop count.val.toNat ∧
      (source_position (stateOf
        (source_readbytes_int (fun bytes => bytes.length)
          readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b (i n)) io)).val =
        (source_position io).val + count.val) ∧
    (∀ {B P N : Type} (length : B → Int) (defaultValue : Int → N)
      (convertInt : N → Except IOErr I) (resize : B → Int → Except IOErr B)
      (checkBounds : B → I → Except IOErr Unit) (pointer : B → P)
      (unsafeRead : BufferState → P → U → M Unit)
      (destinationByte : P → Nat → Option UInt8) (b destination : B)
      (nb : Option N) (requested : I),
      convertInt (nb.getD (defaultValue (length b))) = .ok requested →
      let count := imin requested (source_bytesavailable io)
      (if length b < count.val then resize b count.val = .ok destination else destination = b) →
      (∀ source p transferred, resultOf (unsafeRead source p transferred) source = .ok () →
        ∀ k, k < transferred.val.toNat →
          destinationByte p k = (available source)[k]?) →
      (resultOf (source_readbytes_default length defaultValue convertInt resize checkBounds
        pointer unsafeRead b nb) io = .ok count →
        ∀ k, k < count.val.toNat →
          destinationByte (pointer destination) k = (available io)[k]?) ∧
      (resultOf (source_readbytes_int length resize checkBounds pointer unsafeRead b requested) io =
        .ok count →
        ∀ k, k < count.val.toNat →
          destinationByte (pointer destination) k = (available io)[k]?))

/-- Delimited reads return through the delimiter, honor `keep`, strip CRLF for lines,
and consume exactly those bytes. -/
def ReadUntilSpec : Prop :=
  ∀ io, stateInvariant io → io.readable = true → ∀ delimiter keep,
    (∃ bytes next,
      source_copyuntil (fun out bs => .ok (out ++ bs))
        (fun out bs _ => .ok (out ++ bs)) () () [] io delimiter keep = .ok (bytes, next) ∧
      bytes = untilSpec (available io) delimiter keep ∧
      available next = afterSpec (available io) delimiter) ∧
    (∃ bytes next,
      source_copyline_read (fun out bs => .ok (out ++ bs))
        (fun out bs _ => .ok (out ++ bs)) () () [] io keep = .ok (bytes, next) ∧
      bytes = lineSpec (available io) keep ∧
      available next = afterSpec (available io) 0x0a)

/-- `occursin` searches only the bytes currently available. -/
def OccursinSpec : Prop :=
  ∀ io, stateInvariant io → ∀ delimiter,
    source_occursin delimiter io = .ok (decide (delimiter ∈ available io))

/-- A readable but non-writable buffer returns its contents from the source `take!` method. -/
def TakeReadOnly : Prop :=
  ∀ io, stateInvariant io → io.isMemory = true → io.readable = true → io.writable = false →
    resultOf (source_take_IOBuffer wrapBytes) io =
      .ok (if io.seekable then content io else available io)

/-- After `take!`, even a read-only buffer has position zero. -/
def TakeResets : Prop :=
  ∀ io, stateInvariant io → io.isMemory = true → io.readable = true →
    (∃ bytes, resultOf (source_take_IOBuffer wrapBytes) io = .ok bytes) →
      (source_position (stateOf (source_take_IOBuffer wrapBytes) io)).val = 0

/-- `takestring!` returns a String whose bytes equal the source `take!` result. -/
def TakestringEqTake : Prop :=
  ∀ io, stateInvariant io → io.isMemory = true → ∀ bytes,
    resultOf (source_take_IOBuffer wrapBytes) io = .ok bytes →
      resultOf (source_takestring_IOBuffer unsafeTakeModel copyto unsafeTakeMemoryModel) io =
        .ok ⟨bytes⟩

/-- `readuntil` and `readline` reject unreadable buffers with `ArgumentError`. -/
def ReadUntilUnreadable : Prop :=
  ∀ io, stateInvariant io → io.readable = false → ∀ delimiter keep,
    (∃ msg, source_copyuntil (fun out bs => .ok (out ++ bs))
      (fun out bs _ => .ok (out ++ bs)) () () [] io delimiter keep =
        .error (.jl (.argumentError msg))) ∧
    (∃ msg, source_copyline_read (fun out bs => .ok (out ++ bs))
      (fun out bs _ => .ok (out ++ bs)) () () [] io keep =
        .error (.jl (.argumentError msg)))

/-- Copying a line into the middle of an output buffer has the same state as writing it
without its newline. -/
def CopylineMiddle : Prop :=
  ∀ io, stateInvariant io → io.isMemory = true → io.writable = true → io.append = false →
    io.ptr.val ≤ io.size.val → ∀ line, vectorBytesValid line →
      source_copyline_buffer (fun token => .ok token) copyUntilLineModel copyUntilLineTokenModel
        writeBytesCancelModel () () io line false = writeBytesState io (stripNewline line)

/-- Copying at the end has the same observable buffer state as writing the newline-free line. -/
def CopylineAtEnd : Prop :=
  ∀ io, stateInvariant io → io.writable = true →
    (io.append = true ∨ io.ptr = io.size + i 1) → ∀ line, vectorBytesValid line →
      source_copyline_buffer (fun token => .ok token) copyUntilLineModel copyUntilLineTokenModel
        writeBytesCancelModel () () io line false = writeBytesState io (stripNewline line)

/-- Writing to a writable vector-backed buffer does not fail with `MethodError`. -/
def WriteNoMethodError : Prop :=
  ∀ io, stateInvariant io → io.writable = true → ∀ bytes, vectorBytesValid bytes →
    ∀ fn, resultOf (writeBytesModel bytes) io ≠ .error (.jl (.methodError fn))

/-- `PipeBuffer` accepts the documented integer maxsize types. -/
def PipeBufferMaxsizeInteger : Prop :=
  ∀ t m, t.min ≤ m → m ≤ t.max → 0 ≤ m → m < 2 ^ 63 →
    ∃ io, source_PipeBuffer_maxsize t m = .ok io

/-- Truncation retains a mark that still points within the shortened buffer. -/
def TruncateKeepsMark : Prop :=
  ∀ io, stateInvariant io → ismarked io = true → ∀ n : Int,
    io.mark.val ≤ n → resultOf (source_truncate n) io = .ok () →
      ismarked (stateOf (source_truncate n) io) = true

/-! ## Constructor, representation, and low-level method contracts -/

/-- String-backed allocation and wrapping preserve the requested byte count. -/
def StringMemoryInBounds : Prop :=
  ∀ (stringN : Int → Except IOErr (List UInt8)),
    (∀ n, 0 ≤ n → n ≤ 2 ^ 64 - 1 →
      ∃ bytes, stringN n = .ok bytes ∧ bytes.length = n.toNat) →
    ∀ (wrap : List UInt8 → Except IOErr (List UInt8)),
      (∀ bytes, wrap bytes = .ok bytes) →
      ∀ n, 0 ≤ n → n ≤ 2 ^ 64 - 1 →
        ∃ bytes, source_StringMemory stringN wrap n = .ok bytes ∧ bytes.length = n.toNat

/-- Reads, used spans, takes, and exact-size string copies stay within the backing vector. -/
def IOBufferOperationsInBounds : Prop :=
  ∀ io, stateInvariant io → io.isMemory = true →
    (∀ first last, source_get_used_span io = .ok (first, last) →
      1 ≤ first.val ∧ first.val ≤ last.val + 1 ∧ last.val ≤ io.data.length) ∧
    (io.seekable = false → ismarked io = true →
      source_get_used_span io =
        .ok (imin io.ptr (source_translate_seek_position io io.mark), io.size)) ∧
    (io.seekable = true →
      (∀ byte, resultOf source_read_uint8 io = .ok byte →
        byte = io.data.getD (io.ptr - i 1).val.toNat 0) ∧
      (∀ byte, resultOf source_peek_uint8 io = .ok byte →
        byte = io.data.getD (io.ptr - i 1).val.toNat 0) ∧
      source_unsafe_take
        (fun data start => .ok (data.drop (start.val - 1).toNat)) (.ok [])
        (fun memory n => .ok (memory.take n.val.toNat)) io = .ok (content io) ∧
      resultOf (source_unsafe_takestring unsafeTakeModel copyto unsafeTakeMemoryModel) io =
        .ok ⟨content io⟩ ∧
      (∃ string,
        resultOf (source_takestring_IOBuffer unsafeTakeModel copyto unsafeTakeMemoryModel) io =
          .ok string ∧ string.bytes = content io))
/-- The `show` pointer equals the read position plus one. -/
def ShowPtrPosition : Prop :=
  ∀ io, stateInvariant io →
    ∃ parts, source_show (fun out added => .ok (out ++ added)) [] io = .ok parts ∧
      parts[20]? = some (toString ((source_position io).val + 1))

/-- Before compaction, `show` reports the logical size and one-based pointer. -/
def ShowUncompacted : Prop :=
  ∀ io, stateInvariant io → 0 ≤ io.offset.val →
    ∃ parts, source_show (fun out added => .ok (out ++ added)) [] io = .ok parts ∧
      parts[14]? = some (toString (source_filesize io).val) ∧
      parts[20]? = some (toString ((source_position io).val + 1))

/-- The unchecked constructor initializes observable state from its typed inputs. -/
def NewGenericFields : Prop :=
  ∀ {T : Type} (data : T) (dataBytes : T → List UInt8) (isMemory : T → Bool)
    (readable writable seekable append : Bool) (maxsize : I),
    (dataBytes data).length < 2 ^ 63 →
    let io := source_new_generic_iobuffer data dataBytes isMemory readable writable seekable append maxsize
    source_position io = i 0 ∧
    source_bytesavailable io = i (dataBytes data).length ∧
    source_filesize io = i (dataBytes data).length ∧
    io.data = dataBytes data ∧ io.isMemory = isMemory data ∧ io.reinit = false ∧
    io.readable = readable ∧ io.writable = writable ∧ io.seekable = seekable ∧
    io.append = append ∧ io.maxsize = maxsize ∧ io.ptr = i 1 ∧ io.offset = i 0 ∧
    io.mark = i (-1) ∧
    (readable = true →
      ∀ byte rest, dataBytes data = byte :: rest →
        resultOf source_peek_uint8 io = .ok byte ∧
        resultOf source_read_uint8 io = .ok byte ∧
        available (stateOf source_read_uint8 io) = rest)


/-- Generic constructors apply one-based indexing, the maxsize check, flags, and truncation. -/
def GenericConstructors : Prop :=
  ∀ data readable writable seekable append maxsize truncate io,
    source_GenericIOBuffer_typed (fun _ => .ok ()) data readable writable seekable append
      maxsize truncate = .ok io →
    io.readable = readable ∧ io.writable = writable ∧ io.seekable = seekable ∧
    io.append = append ∧ io.maxsize = i maxsize ∧
    (truncate = true → io.size = io.offset) ∧ stateInvariant io

/-- The vector overload keeps the view's memory offset and length. -/
def VectorConstructor : Prop :=
  ∀ v readable writable seekable append maxsize truncate io,
    source_GenericIOBuffer_Vector v readable writable seekable append maxsize truncate = .ok io →
    io.offset = i v.off ∧ io.ptr = i (v.off + 1) ∧
    io.size = i (if truncate then v.off else v.len + v.off) ∧ io.isMemory = true

/-- Compaction removes the storage offset without changing the logical read position. -/
def OffsetAccessors : Prop :=
  ∀ io, stateInvariant io →
    source_get_offset io - source_get_compacted io = io.offset ∧
    (source_get_offset io = i 0 ∨ source_get_compacted io = i 0) ∧
    (∀ removed, resultOf source_compact io = .ok removed →
      source_get_offset (stateOf source_compact io) = i 0 ∧
      source_position (stateOf source_compact io) = source_position io)

/-- StringVector preserves allocator bytes and the requested length. -/
def StringAllocators : Prop :=
  ∀ (stringN : Int → Except IOErr (List UInt8))
    (unsafeWrap wrapArray : List UInt8 → Except IOErr (List UInt8)),
    (∀ bytes, unsafeWrap bytes = .ok bytes) →
    (∀ bytes, wrapArray bytes = .ok bytes) →
    ∀ n bytes, 0 ≤ n → n ≤ 2 ^ 64 - 1 →
      stringN n = .ok bytes → bytes.length = n.toNat →
      source_StringVector stringN unsafeWrap wrapArray n = .ok bytes

/-- Public constructors preserve their selected capabilities and create valid buffer states. -/
def PublicConstructors : Prop :=
  (∀ data (read write append truncate : Option Bool) maxsize io,
    0 ≤ maxsize → maxsize < 2 ^ 63 → (dataBytes data).length < 2 ^ 63 →
    source_IOBuffer_data (fun d _ => .ok d) data read write append truncate maxsize none = .ok io →
      let flags := openFlags read write none truncate append
      io.readable = flags.read ∧ io.writable = flags.write ∧ io.seekable = true ∧
      io.append = flags.append ∧ stateInvariant io) ∧
  (∀ (read write append truncate : Option Bool) maxsize hint io,
    0 ≤ maxsize → maxsize < 2 ^ 63 →
    (hint = none ∨ ∃ n, hint = some n ∧ -(2 ^ 63) ≤ n ∧ n < 2 ^ 63) →
    source_IOBuffer_empty read write append truncate maxsize hint = .ok io →
      let flags := openFlags read write none truncate append
      io.readable = flags.read ∧ io.writable = flags.write ∧ io.seekable = true ∧
      io.append = flags.append ∧ io.size = i 0 ∧ stateInvariant io) ∧
  (∀ data maxsize io, 0 ≤ maxsize.val →
    source_PipeBuffer_data data maxsize = .ok io →
      io.readable = true ∧ io.writable = true ∧ io.seekable = false ∧
      io.append = true ∧ io.maxsize = maxsize ∧ stateInvariant io)

/-- An internal truncated pipe is empty, reports EOF, and retains its requested size limit. -/
def TruncatedPipeCorrect : Prop :=
  ∀ data maxsize io,
    source_truncated_pipebuffer data maxsize = .ok io →
      io.size = source_get_offset io ∧ source_filesize io = i 0 ∧
      source_bytesavailable io = i 0 ∧ source_eof io = true ∧ io.maxsize = maxsize ∧
      resultOf source_read_uint8 io = .error .eofError

/-- Both storage helpers preserve the length guaranteed by the external allocator. -/
def SimilarDataCorrect : Prop :=
  ∀ (similar : List UInt8 → I → Except IOErr (List UInt8))
    (stringN : Int → Except IOErr (List UInt8))
    (wrap : List UInt8 → Except IOErr (List UInt8)),
    (∀ bytes, wrap bytes = .ok bytes) →
    ∀ b n genericBytes memoryBytes, 0 ≤ n.val →
      similar b.data n = .ok genericBytes → genericBytes.length = n.val.toNat →
      stringN n.val = .ok memoryBytes → memoryBytes.length = n.val.toNat →
      source_similar_data_generic similar b n = .ok genericBytes ∧
      source_similar_data_IOBuffer (source_StringMemory stringN wrap) b n = .ok memoryBytes ∧
      genericBytes.length = memoryBytes.length

/-- Copy preserves available bytes and capabilities for every ownership branch. -/
def CopyReadonlyFields : Prop :=
  ∀ b similar copied, stateInvariant b →
    copyModel similar b = .ok copied →
      (b.writable = false →
        copied.data = b.data ∧ copied.ptr = b.ptr ∧ copied.mark = b.mark ∧
        copied.offset = b.offset) ∧
      (b.reinit = false →
        available copied = available b ∧ source_position copied = source_position b ∧
        copied.mark = b.mark) ∧
      copied.readable = b.readable ∧ copied.writable = b.writable ∧
      copied.seekable = b.seekable ∧ copied.append = b.append ∧ copied.maxsize = b.maxsize

/-- The unreadable helper throws the documented error, which byte reads and peeks propagate. -/
def ThrowNotReadable : Prop :=
  (∀ α, (source_throw_not_readable : Except IOErr α) =
    .error (.jl (.argumentError "read failed, IOBuffer is not readable"))) ∧
  ∀ io, stateInvariant io → io.readable = false →
    resultOf source_read_uint8 io =
      .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
    resultOf source_peek_uint8 io =
      .error (.jl (.argumentError "read failed, IOBuffer is not readable"))

/-- The vector and dense `unsafe_read!` methods transfer consecutive source bytes. -/
def UnsafeReadMethods : Prop :=
  ∀ (src : List UInt8) (dest : Nat) (start : Int) (count : Nat),
    1 ≤ start → (start - 1).toNat + count ≤ src.length →
    count ≤ 2 ^ 64 - 1 →
    source_unsafe_read_vector
      (fun data index => data.getD (index - 1).toNat 0)
      (fun pointer byte offset =>
        if pointer = dest ∧ 1 ≤ offset.val ∧
          src[(start + offset.val - 1).toNat]? = some byte
        then .ok () else .error .outOfBounds)
      dest src start (u count) = .ok () ∧
    source_unsafe_read_dense
      (fun _ destination sourcePointer n =>
        if destination = dest ∧ sourcePointer = start.toNat ∧ n.val = count
        then .ok () else .error .outOfBounds)
      (fun _ index => index.toNat) dest src start (u count) = .ok ()

/-- Little-endian loading equals the base-256 value of the selected bytes. -/
def LoadFromArrayLittleEndian : Prop :=
  ∀ (data : List UInt8) (start width : Nat), start + width ≤ data.length →
    data.length < 2 ^ 63 →
    source_load_from_array false 0 0 (fun _ => width)
      (fun bytes index => bytes.getD (index - 1).toNat 0)
      UInt8.toNat Nat.shiftLeft Nat.lor id id data (i (start + 1)) =
        ((List.range width).map
          (fun k => (data.getD (start + k) 0).toNat * 256 ^ k)).sum


/-- Both source multibyte peek paths leave the buffer pointer unchanged. -/
def PeekMethodsDoNotAdvance : Prop :=
  ∀ io, stateInvariant io → ∀ {T : Type} (isFloat : Bool) (uintZero unsignedZero : T)
    (sizeOf : T → Nat) (convertByte : UInt8 → T) (shift : T → Nat → T)
    (bitOr : T → T → T) (ltoh reinterpret : T → T) (value : T),
    stateOf (peekArrayModel isFloat uintZero unsignedZero sizeOf convertByte shift bitOr
      ltoh reinterpret value) io = io ∧
    ∀ {P : Type} (pointer : BufferState → Int → P) (unsafeLoad : P → Except IOErr T)
      (withPreserve : BufferState → (P → Except IOErr T) → Except IOErr T),
      stateOf (source_peek_multibyte_dense sizeOf pointer unsafeLoad withPreserve value) io = io

/-- Source multibyte reads return the peeked value and advance one value width. -/
def ReadMultiAdvances : Prop :=
  ∀ io, stateInvariant io → ∀ {T : Type} (isFloat : Bool) (uintZero unsignedZero : T)
    (sizeOf : T → Nat) (convertByte : UInt8 → T) (shift : T → Nat → T)
    (bitOr : T → T → T) (ltoh reinterpret : T → T) (typeValue value : T),
    let peek := peekArrayModel isFloat uintZero unsignedZero sizeOf convertByte shift bitOr
      ltoh reinterpret
    resultOf (peek typeValue) io = .ok value →
      resultOf (source_read_multibyte peek sizeOf typeValue) io = .ok value ∧
      (source_position (stateOf (source_read_multibyte peek sizeOf typeValue) io)).val =
        (source_position io).val + sizeOf typeValue

/-- Pointer reads convert the source UInt reader's value and consume the same bytes. -/
def PtrReadIsUIntRead : Prop :=
  ∀ io, stateInvariant io → ∀ {P : Type} (convert : U → P) value,
    resultOf readUIntModel io = .ok value →
      resultOf (source_read_pointer readUIntModel convert) io = .ok (convert value) ∧
      stateOf (source_read_pointer readUIntModel convert) io = stateOf readUIntModel io

/-- Closing writes preserves reads and rejects every later byte write. -/
def ReadWriteFlags : Prop :=
  ∀ io, stateInvariant io →
    source_isreadable io = io.readable ∧ source_iswritable io = io.writable ∧
    source_isreadable (stateOf source_closewrite io) = io.readable ∧
    source_iswritable (stateOf source_closewrite io) = false ∧
    resultOf source_read_uint8 (stateOf source_closewrite io) = resultOf source_read_uint8 io ∧
    (∀ byte, resultOf (writeByteModel byte) (stateOf source_closewrite io) =
      .error (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable")))

/-- Seeking, seekend, and translation preserve the documented clamped position rules. -/
def SeekMethodsCorrect : Prop :=
  ∀ io, stateInvariant io → ∀ n,
    (io.seekable = true → resultOf (source_seek n) io = .ok () →
      0 ≤ (source_position (stateOf (source_seek n) io)).val ∧
      (source_position (stateOf (source_seek n) io)).val ≤ (source_filesize io).val) ∧
    (source_position (stateOf source_seekend io)).val = (source_filesize io).val ∧
    source_translate_seek_position io n = clampToI (n.val + io.offset.val + 1)

/-- Room checks preserve sufficient storage, reject non-writable states, and check signed counts. -/
def EnsureRoomMethods : Prop :=
  ∀ io, stateInvariant io →
    (∀ n : U, io.writable = true → io.reinit = false →
      let start := if io.append then io.size else io.ptr - i 1
      let space := imin (i io.data.length - start) (io.maxsize - (start - getOffset io))
      space.val ≥ (JInt.rem .i64 n).val →
        resultOf (ensureRoomModel n) io = .ok () ∧ stateOf (ensureRoomModel n) io = io) ∧
    (∀ n : U, io.writable = false →
      resultOf (ensureRoomModel n) io =
        .error (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable"))) ∧
    (∀ n : I, n.val < 0 →
      resultOf (source_ensureroom_int (fun _ count => ensureRoomModel count) io n) io =
        .error (.jl (.inexactError "convert")))

/-- close releases capabilities and resets size, maxsize, pointer and mark. -/
def CloseMethodCorrect : Prop :=
  ∀ io, stateInvariant io → ∀ resize,
    resultOf (source_close resize) io = .ok () →
      let closed := stateOf (source_close resize) io
      closed.readable = false ∧ closed.writable = false ∧ closed.seekable = false ∧
      closed.size = i 0 ∧ closed.maxsize = i 0 ∧ closed.ptr = i 1 ∧ closed.mark = i (-1)

/-- Successful reads require an open buffer; close shuts it and closewrite preserves readable data. -/
def IsopenCorrect : Prop :=
  ∀ io, stateInvariant io →
    (∀ byte, resultOf source_read_uint8 io = .ok byte →
      source_isopen source_bytesavailable io = true) ∧
    source_isopen source_bytesavailable
      (stateOf (source_close (fun size exact => resize size exact)) io) = false ∧
    (io.readable = true → source_isopen source_bytesavailable (stateOf source_closewrite io) = true) ∧
    (0 < (source_bytesavailable io).val →
      source_isopen source_bytesavailable (stateOf source_closewrite io) = true)

/-- Generic and IOBuffer take methods return retained bytes and reset writable buffers. -/
def TakeMethodsCorrect : Prop :=
  ∀ io, stateInvariant io → io.writable = true → io.isMemory = true →
    ∃ bytes, resultOf (source_take_generic (fun count => readBang count)) io = .ok bytes ∧
      resultOf (source_takestring_generic (fun count => readBang count)) io = .ok ⟨bytes⟩ ∧
      resultOf (source_take_IOBuffer wrapBytes) io =
        .ok (if io.seekable then content io else available io) ∧
      (stateOf (source_take_generic (fun count => readBang count)) io).reinit = true ∧
      (stateOf (source_take_IOBuffer wrapBytes) io).reinit = true

/-- The unsafe take view contains exactly the used bytes. -/
def UnsafeTakeReturnsUsed : Prop :=
  ∀ io, stateInvariant io → io.isMemory = true → io.seekable = true →
    source_unsafe_take (fun data start => .ok (slice data start.val io.size.val)) (.ok [])
      (fun bytes n => .ok (bytes.take n.val.toNat)) io = .ok (content io)

/-- Writing another buffer consumes its unread bytes, and self-copy is rejected before writing. -/
def WriteFromConsumes : Prop :=
  ∀ io, stateInvariant io → ∀ {Out : Type}
    (same : Out → BufferState → Bool) (write : Out → List UInt8 → Except IOErr I) out,
    (same out io = true →
      resultOf (source_write_buffer_to_IO same write out) io =
        .error (.jl (.argumentError "writing all content from an IOBuffer into itself is invalid")) ∧
      stateOf (source_write_buffer_to_IO same write out) io = io) ∧
    (same out io = false → io.readable = true → ∀ count,
      write out (available io) = .ok count →
        resultOf (source_write_buffer_to_IO same write out) io = .ok count ∧
        available (stateOf (source_write_buffer_to_IO same write out) io) = [] ∧
        (source_position (stateOf (source_write_buffer_to_IO same write out) io)).val =
          (io.size + i 1 - io.offset).val)

/-- The vector write stores pointer bytes; large dense writes call the copy callback at the exact range. -/
def UnsafeWriteMethods : Prop :=
  ∀ (data src : List UInt8) (start : Int) (p count : Nat),
    1 ≤ start → (start - 1).toNat + count ≤ data.length →
    p + count ≤ src.length → data.length < 2 ^ 63 →
    let expected := data.take (start - 1).toNat ++
      (src.drop p).take count ++ data.drop ((start - 1).toNat + count)
    (∃ updated,
      source_unsafe_write_vector
        (fun bytes index byte => setChecked bytes (i index) byte)
        (fun pointer => match src[pointer]? with
          | some byte => .ok byte
          | none => .error .outOfBounds)
        Nat.succ data p start (u count) = .ok (updated, p + count) ∧
      updated = expected) ∧
    (count < 5 →
      source_unsafe_write_dense
        (fun bytes index byte => setChecked bytes (i index) byte)
        (fun pointer offset => match src[pointer + offset.val.toNat - 1]? with
          | some byte => .ok byte
          | none => .error .outOfBounds)
        (fun _ startIndex => (startIndex - 1).toNat)
        (fun destination sourcePointer n =>
          if destination = (start - 1).toNat ∧ sourcePointer = p ∧ n.val = count
          then .ok () else .error .outOfBounds)
        data p start (u count) = .ok expected) ∧
    (5 ≤ count →
      source_unsafe_write_dense
        (fun bytes index byte => setChecked bytes (i index) byte)
        (fun pointer offset => match src[pointer + offset.val.toNat - 1]? with
          | some byte => .ok byte
          | none => .error .outOfBounds)
        (fun _ startIndex => (startIndex - 1).toNat)
        (fun destination sourcePointer n =>
          if destination = (start - 1).toNat ∧ sourcePointer = p ∧ n.val = count
          then .ok () else .error .outOfBounds)
        data p start (u count) = .ok data)

/-- A one-byte write followed by a one-byte read returns that byte when capacity allows. -/
def ByteReadWriteMethods : Prop :=
  ∀ io, stateInvariant io → io.writable = true → io.readable = true →
    io.seekable = true → io.append = false → ∀ byte,
      (io.maxsize.val > (source_position io).val) →
      resultOf (writeByteModel byte) io = .ok (i 1) →
      resultOf source_read_uint8 (stateOf (writeByteModel byte) io) = .ok byte

/-- The buffer line readers return through the newline, strip CRLF when requested, and write the same bytes to IO or IOBuffer outputs. -/
def CopylineMethods : Prop :=
  ∀ io, stateInvariant io → io.readable = true → ∀ keep,
    (∃ bytes next,
      source_copyline_read (fun out bs => .ok (out ++ bs))
        (fun out bs _ => .ok (out ++ bs)) () () [] io keep = .ok (bytes, next) ∧
      bytes = lineSpec (available io) keep ∧ available next = afterSpec (available io) 0x0a) ∧
    (∃ bytes next,
      source_copyline_IO (fun out bs => .ok (out ++ bs))
        (fun out bs _ => .ok (out ++ bs)) () () [] io keep = .ok (bytes, next) ∧
      bytes = lineSpec (available io) keep ∧ available next = afterSpec (available io) 0x0a) ∧
    (∀ out, stateInvariant out → out.writable = true →
      ∃ bytes outNext inNext,
        bytes = lineSpec (available io) keep ∧
        writeBytesState out bytes = .ok outNext ∧
        source_copyline_buffer_buffer writeBytesState writeBytesCancelModel () () out io keep =
          .ok (outNext, inNext) ∧ available inNext = afterSpec (available io) 0x0a) ∧
    (∀ out next, stateInvariant out → out.writable = true →
      writeBytesState out (lineSpec (available io) keep) = .ok next →
      source_copyline_buffer (fun token => .ok token) copyUntilLineModel copyUntilLineTokenModel
        writeBytesCancelModel () () out (available io) keep = .ok next)

/-- CRC results cover the unread prefix, consume its bytes, and preserve documented errors. -/
def CrcDefaultUsesAvailable : Prop :=
  ∀ (checksum : List UInt8 → UInt32 → UInt32)
    (unsafeCRC : (List UInt8 × I) → I → UInt32 → Except IOErr UInt32),
    (∀ seed, checksum [] seed = seed) →
    (∀ data (ptr count : I) seed, 0 ≤ count.val → 1 ≤ ptr.val →
      ptr.val + count.val - 1 ≤ data.length →
      unsafeCRC (data, ptr) count seed =
        .ok (checksum (slice data ptr.val (ptr.val + count.val - 1)) seed)) →
    ∀ io, stateInvariant io → ∀ (n : Int) (seed : Option UInt32),
      let pointer := fun (buffer : BufferState) (index : I) => (buffer.data, index)
      let initial := seed.getD 0
      (n < 0 →
        resultOf (source_crc32c_bytes unsafeCRC pointer n seed) io =
          .error (.jl (.argumentError
            ("number of bytes to checksum must be ≥ 0, got " ++ toString n)))) ∧
      (0 ≤ n → io.readable = false →
        resultOf (source_crc32c_bytes unsafeCRC pointer n seed) io =
          .error (.jl (.argumentError "read failed, IOBuffer is not readable"))) ∧
      (0 ≤ n → io.readable = true →
        let count := min n (source_bytesavailable io).val
        resultOf (source_crc32c_bytes unsafeCRC pointer n seed) io =
          .ok (checksum ((available io).take count.toNat) initial) ∧
        (source_bytesavailable
          (stateOf (source_crc32c_bytes unsafeCRC pointer n seed) io)).val =
            (source_bytesavailable io).val - count) ∧
      (io.readable = true →
        resultOf (source_crc32c_default unsafeCRC pointer seed) io =
          .ok (checksum (available io) initial) ∧
        available (stateOf (source_crc32c_default unsafeCRC pointer seed) io) = [])

/-! ## Additional user-requested read, write, and position statements -/

/-- readavailable returns all unread bytes, read(n) returns its available prefix, and peek does not advance. -/
def ReadAvailableAndPeekCounts : Prop :=
  ∀ io, stateInvariant io → io.readable = true →
    resultOf (source_readavailable (fun count => readBang count)) io = .ok (available io) ∧
    (source_bytesavailable (stateOf (source_readavailable (fun count => readBang count)) io)).val = 0 ∧
    (source_position (stateOf (source_readavailable (fun count => readBang count)) io)).val =
      (source_position io).val + (source_bytesavailable io).val ∧
    (∀ n : Int, 0 ≤ n →
      resultOf (source_read_n (fun count => readBang count) n) io =
        .ok ((available io).take n.toNat)) ∧
    (∀ byte, available io = byte :: (available io).drop 1 →
      resultOf source_peek_uint8 io = .ok byte ∧ stateOf source_peek_uint8 io = io)

/-- Writes on non-writable buffers and reads on non-readable buffers raise their documented ArgumentErrors. -/
def ReadWritePermissionErrors : Prop :=
  ∀ io, stateInvariant io → ∀ bytes, vectorBytesValid bytes →
    (io.writable = false →
      resultOf (writeBytesModel bytes) io =
        .error (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable")) ∧
      stateOf (writeBytesModel bytes) io = io ∧
      (∀ byte,
        resultOf (source_write_uint8 ensureRoomModel
          (fun state ptr value => setChecked state.data ptr value) byte) io =
            .error (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable")) ∧
        stateOf (source_write_uint8 ensureRoomModel
          (fun state ptr value => setChecked state.data ptr value) byte) io = io)) ∧
    (io.readable = false →
      resultOf source_read_uint8 io =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
      stateOf source_read_uint8 io = io ∧
      resultOf source_peek_uint8 io =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
      stateOf source_peek_uint8 io = io ∧
      (∀ n : Int, 0 ≤ n →
        resultOf (source_read_n (fun count => readBang count) n) io =
          .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
        stateOf (source_read_n (fun count => readBang count) n) io = io) ∧
      resultOf (source_readavailable (fun count => readBang count)) io =
        .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
      stateOf (source_readavailable (fun count => readBang count)) io = io ∧
      (∀ b, b.length < 2 ^ 63 →
        resultOf (source_readbytes_default (fun value => value.length) id toI
          readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b none) io =
            .error (.jl (.argumentError "read failed, IOBuffer is not readable")) ∧
        stateOf (source_readbytes_default (fun value => value.length) id toI
          readbytesResizeModel readbytesBoundsModel (fun _ => ()) readbytesAdvanceModel b none) io =
            io))

/-- A successful source write never advances beyond the configured `maxsize` boundary. -/
def MaxsizeCapsWrites : Prop :=
  ∀ io, stateInvariant io → io.writable = true → ∀ bytes, vectorBytesValid bytes →
    let ensureRoom := ensureRoomModel
    let write := source_unsafe_write (fun _ => .ok ()) ensureRoom writePointerModel
      () bytes (u bytes.length)
    let room := stateOf (ensureRoom (u bytes.length)) io
    let startOffset := if room.append then room.size else room.ptr - i 1
    ∃ count, resultOf (ensureRoom (u bytes.length)) io = .ok () ∧ stateInvariant room ∧
      resultOf write io = .ok count ∧
      count.val ≤ bytes.length ∧
      count.val ≤ max 0 (room.maxsize.val - (startOffset - getOffset room).val)

/-- Successful source seek/skip/truncate and typed mark/reset methods keep position in range. -/
def PositionBoundsAfterOperations : Prop :=
  ∀ (markMethod resetMethod : M I),
    (∀ io, stateInvariant io →
      resultOf markMethod io = .ok (source_position io) ∧
      (stateOf markMethod io).mark = source_position io) →
    (∀ io, stateInvariant io → ismarked io = true →
      resultOf resetMethod io = .ok io.mark ∧
      source_position (stateOf resetMethod io) = io.mark) →
    (∀ io, stateInvariant io → ismarked io = false →
      resultOf resetMethod io = .error (.jl (.argumentError "IOBuffer not marked"))) →
    ∀ io, stateInvariant io → ∀ n : Int,
      (resultOf (source_seek (clampToI n)) io = .ok () →
        positionWithin (stateOf (source_seek (clampToI n)) io)) ∧
      (resultOf (source_skip source_seek (clampToI n)) io = .ok () →
        positionWithin (stateOf (source_skip source_seek (clampToI n)) io)) ∧
      (resultOf markMethod io = .ok (source_position io) →
        positionWithin (stateOf markMethod io)) ∧
      (resultOf (source_truncate n) io = .ok () →
        positionWithin (stateOf (source_truncate n) io)) ∧
      (resultOf resetMethod io = .ok io.mark →
        positionWithin (stateOf resetMethod io))

/-! ## Registry entries -/

/-! Nothing to promise:
`GenericIOBuffer@134` forwards the same arguments to `GenericIOBuffer{T}@110`.
`readavailable@980` forwards to `read@977`; its documented byte behavior is stated by
`ReadAvailableAndPeekCounts`.
`copyline@1079` and `copyline@1080` forward unchanged to `_copyline@1057`; their
documented byte behavior is stated by `CopylineMethods`.
-/

def entries : List Entry := [
  { id := "iobuffers-invariant", juliaFile := "base/iobuffer.jl",
    juliaFns := ["position", "bytesavailable", "eof", "filesize", "write", "read(::GenericIOBuffer, ::Type{UInt8})", "seek", "skip", "truncate", "compact!", "take!", "closewrite", "close"],
    statement := "Valid states keep position between zero and logical size; bytesavailable is nonnegative, eof means no bytes remain, and seekable position plus bytesavailable equals filesize. Successful state-changing methods preserve the field invariant.", source := "invariant base/iobuffer.jl:55-93 (field comments)",
    status := .todo, prop := ``InvariantHolds, thm := none },
  { id := "iobuffers-no-out-of-bounds", juliaFile := "base/iobuffer.jl",
    juliaFns := ["unsafe_write", "unsafe_read", "read(::GenericIOBuffer, ::Type{UInt8})", "peek", "compact!", "_resize!"],
    statement := "Every operation on a reachable buffer reads or writes only within its allocated memory.", source := "invariant base/iobuffer.jl:55-70",
    status := .todo, prop := ``NoOutOfBounds, thm := none },
  { id := "iobuffers-write-at-position", juliaFile := "base/iobuffer.jl",
    juliaFns := ["unsafe_write(::GenericIOBuffer, ::Ptr{UInt8}, ::UInt)", "ensureroom"],
    statement := "write on a seekable non-append IOBuffer overwrites from the position, writes min(n, maxsize - position) bytes and advances the position by that much.", source := "base/iobuffer.jl:173-180 (IOBuffer docstring: maxsize), 67-69",
    status := .todo, prop := ``WriteAtPosition, thm := none },
  { id := "iobuffers-append-at-end", juliaFile := "base/iobuffer.jl",
    juliaFns := ["unsafe_write(::GenericIOBuffer, ::Ptr{UInt8}, ::UInt)", "PipeBuffer"],
    statement := "write on an append buffer adds min(n, maxsize - retained bytes) bytes at the end and leaves the position alone, also across compaction.", source := "base/iobuffer.jl:52-53 (append writes to size+1), 278 (PipeBuffer performs writes by appending)",
    status := .todo, prop := ``AppendWritesAtEnd, thm := none },
  { id := "iobuffers-write-read-roundtrip", juliaFile := "base/iobuffer.jl",
    juliaFns := ["IOBuffer(; maxsize)", "write", "seekstart", "read(::GenericIOBuffer)"],
    statement := "IOBuffer(maxsize=m), any writes, seekstart, read returns the first m bytes written.", source := "base/iobuffer.jl:180, 214-221 (maxsize docstring and example)",
    status := .todo, prop := ``WriteReadRoundtrip, thm := none },
  { id := "iobuffers-pipe-fifo", juliaFile := "base/iobuffer.jl",
    juliaFns := ["PipeBuffer", "write", "read(::GenericIOBuffer, ::Type{UInt8})", "read(::GenericIOBuffer, nb)", "read(::GenericIOBuffer)"],
    statement := "On a PipeBuffer, bytes read and still available equal the initially unread bytes plus bytes accepted by writes, preserving order under every interleaving.", source := "base/iobuffer.jl:272-283 (PipeBuffer behaves like a Unix pipe)",
    status := .todo, prop := ``PipeFIFO, thm := none },
  { id := "iobuffers-pipe-mark-reset", juliaFile := "base/iobuffer.jl",
    juliaFns := ["mark", "reset", "compact!", "get_used_span", "PipeBuffer"],
    statement := "On a PipeBuffer, reset after mark restores the marked position and makes every byte accepted by later writes available, even after reads and compaction.", source := "base/io.jl:1569-1606 (mark/reset docstrings); base/iobuffer.jl:44-46",
    status := .todo, prop := ``PipeMarkReset, thm := none },
  { id := "iobuffers-seek", juliaFile := "base/iobuffer.jl",
    juliaFns := ["seek(::GenericIOBuffer, ::Integer)", "seekstart"],
    statement := "seek(io, n) on a seekable buffer moves to clamp(n, 0, filesize); on a pipe it throws unless n == mark, and then moves to the mark.", source := "base/iostream.jl:144-146 (seek docstring), base/iobuffer.jl:512-524",
    status := .todo, prop := ``SeekSpec, thm := none },
  { id := "iobuffers-skip", juliaFile := "base/iobuffer.jl",
    juliaFns := ["skip(::GenericIOBuffer, ::Integer)"],
    statement := "skip(io, n) moves by min(n, bytesavailable) for n >= 0 and to max(0, position + n) for n < 0 on seekable buffers, for every Int n including typemin/typemax.", source := "base/iostream.jl skip docstring (seek relative to the current position), base/iobuffer.jl:475-494",
    status := .todo, prop := ``SkipSpec, thm := none },
  { id := "iobuffers-truncate", juliaFile := "base/iobuffer.jl",
    juliaFns := ["truncate(::GenericIOBuffer, ::Integer)"],
    statement := "truncate(io, n) throws ArgumentError exactly when not writable, not seekable, n < 0 or n > maxsize; otherwise the buffer holds its old bytes cut or zero-padded to n and position <= n.", source := "base/iobuffer.jl:558-593; truncate docstring (base/iostream.jl)",
    status := .todo, prop := ``TruncateSpec, thm := none },
  { id := "iobuffers-take", juliaFile := "base/iobuffer.jl",
    juliaFns := ["take!(::IOBuffer)"],
    statement := "take! on a writable IOBuffer returns all bytes (the unread bytes of a pipe) and leaves position, bytesavailable and filesize 0 and no mark.", source := "base/iobuffer.jl:716-718 (take! docstring)",
    status := .todo, prop := ``TakeSpec, thm := none },
  { id := "iobuffers-read", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer, nb)", "readbytes!", "read(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::Type{UInt8})"],
    statement := "read(io, n) and readbytes! return the next min(n, bytesavailable) bytes and advance by that much; read(io, UInt8) returns the next byte or throws EOFError; peek does not move.", source := "base/io.jl:1295-1330 (read and readbytes! docstrings)",
    status := .todo, prop := ``ReadSpec, thm := none },
  { id := "iobuffers-readuntil", juliaFile := "base/iobuffer.jl",
    juliaFns := ["readuntil(::IO, ::UInt8)", "copyuntil(::IO, ::GenericIOBuffer, ::UInt8)", "readline", "_copyline"],
    statement := "readuntil(io, d; keep) and readline(io; keep) return the bytes up to the delimiter (with it iff keep; readline also strips \\r\\n) and consume through the delimiter.", source := "base/io.jl:640-648 (copyuntil docstring), 719-728 (copyline docstring)",
    status := .todo, prop := ``ReadUntilSpec, thm := none },
  { id := "iobuffers-occursin", juliaFile := "base/iobuffer.jl",
    juliaFns := ["occursin(::UInt8, ::GenericIOBuffer)"],
    statement := "occursin(d, io) tells whether d is among the bytes available.", source := "invariant (base/iobuffer.jl:984-986)",
    status := .todo, prop := ``OccursinSpec, thm := none },
  { id := "iobuffers-take-closewrite", juliaFile := "base/iobuffer.jl",
    juliaFns := ["take!(::IOBuffer)", "closewrite(::GenericIOBuffer)"],
    statement := "take! on a readable IOBuffer that is not writable returns its contents (the unread bytes of a pipe).", source := "base/iobuffer.jl:716-718 (take! docstring)",
    status := .todo, prop := ``TakeReadOnly, thm := none },
  { id := "iobuffers-take-readonly-reset", juliaFile := "base/iobuffer.jl",
    juliaFns := ["take!(::IOBuffer)"],
    statement := "After take!(io) the IOBuffer is reset to its initial state (position 0).", source := "base/iobuffer.jl:716-718 (take! docstring: Afterwards, the IOBuffer is reset to its initial state)",
    status := .todo, prop := ``TakeResets, thm := none },
  { id := "iobuffers-takestring-mark", juliaFile := "base/iobuffer.jl",
    juliaFns := ["takestring!(::IOBuffer)"],
    statement := "takestring!(io) returns the same bytes as String(take!(io)).", source := "base/iobuffer.jl:812-817 (takestring! docstring)",
    status := .todo, prop := ``TakestringEqTake, thm := none },
  { id := "iobuffers-readuntil-unreadable", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copyuntil(::IO, ::GenericIOBuffer, ::UInt8)", "_copyline(::IO, ::GenericIOBuffer)"],
    statement := "readuntil and readline on an IOBuffer that is not readable throw ArgumentError, like read.", source := "base/iobuffer.jl:178 (read keyword restricts operations), 344-350",
    status := .todo, prop := ``ReadUntilUnreadable, thm := none },
  { id := "iobuffers-copyline-middle", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copyline(::GenericIOBuffer, ::IO)"],
    statement := "copyline(out::IOBuffer, s; keep=false) into the middle of out writes the line without its newline.", source := "base/io.jl:724-728 (copyline docstring)",
    status := .todo, prop := ``CopylineMiddle, thm := none },
  { id := "iobuffers-copyline-prior", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copyline(::GenericIOBuffer, ::IO)"],
    statement := "copyline(out::IOBuffer, s; keep=false) at the end of out leaves the bytes already in out untouched.", source := "base/io.jl:718-728 (copyline docstring)",
    status := .todo, prop := ``CopylineAtEnd, thm := none },
  { id := "iobuffers-view-grow", juliaFile := "base/iobuffer.jl",
    juliaFns := ["ensureroom_slowpath", "get_used_span(::IOBuffer)", "_similar_data(::GenericIOBuffer, ::Int)"],
    statement := "write to a writable buffer over any AbstractVector{UInt8} does not throw MethodError.", source := "base/iobuffer.jl:173-193 (IOBuffer docstring)",
    status := .todo, prop := ``WriteNoMethodError, thm := none },
  { id := "iobuffers-pipebuffer-maxsize-type", juliaFile := "base/iobuffer.jl",
    juliaFns := ["PipeBuffer(data; maxsize)", "PipeBuffer(maxsize::Integer)"],
    statement := "PipeBuffer accepts maxsize of any Integer type, as documented.", source := "base/iobuffer.jl:276 (PipeBuffer docstring: maxsize::Integer)",
    status := .todo, prop := ``PipeBufferMaxsizeInteger, thm := none },
  { id := "iobuffers-truncate-mark", juliaFile := "base/iobuffer.jl",
    juliaFns := ["truncate(::GenericIOBuffer, ::Integer)"],
    statement := "truncate(io, n) keeps a mark at a position <= n.", source := "base/iobuffer.jl:578 (comment: clear the mark if it points to data that has now been deleted)",
    status := .todo, prop := ``TruncateKeepsMark, thm := none },
  { id := "memsafety-iobuffer-string-memory", juliaFile := "base/iobuffer.jl",
    juliaFns := ["StringMemory"],
    statement := "On successful Csize_t conversion, _string_n allocates exactly n bytes and unsafe_wrap exposes those same n bytes as Memory.", source := "base/iobuffer.jl:166-168; base/strings/string.jl:184-185",
    status := .todo, prop := ``StringMemoryInBounds, thm := none },
  { id := "memsafety-iobuffer-operations", juliaFile := "base/iobuffer.jl",
    juliaFns := ["peek", "read", "take!", "get_used_span", "mark", "reset", "unsafe_takestring!", "takestring!", "_unsafe_take!"],
    statement := "The documented IOBuffer field invariant bounds the computed read pointer, take view, translated marked span, and both exact-size string copies.", source := "base/iobuffer.jl:55-93,406-448,661-673,758-859; JuliaLean.IOBuffers.reachable_inv",
    status := .todo, prop := ``IOBufferOperationsInBounds, thm := none },
  { id := "iocov-iobuffer-show-compacted", juliaFile := "base/iobuffer.jl",
    juliaFns := ["show(::IO, ::GenericIOBuffer)"],
    statement := "The ptr printed by show(::IOBuffer) is the read position plus one, as the skipchars docstring example shows.", source := "base/io.jl:1628-1632 (skipchars docstring example)",
    status := .todo, prop := ``ShowPtrPosition, thm := none },
  { id := "iocov-iobuffer-show", juliaFile := "base/iobuffer.jl",
    juliaFns := ["show(::IO, ::GenericIOBuffer)", "get_offset", "get_compacted"],
    statement := "For a buffer that was never compacted, show prints ptr = position + 1 and the size relative to the offset.", source := "base/iobuffer.jl:334-342 (invariant)",
    status := .todo, prop := ``ShowUncompacted, thm := none },
  { id := "iocov-iobuffer-new", juliaFile := "base/iobuffer.jl",
    juliaFns := ["_new_generic_iobuffer"],
    statement := "The unchecked constructor initializes every field from the data and flags.", source := "base/iobuffer.jl:96-107",
    status := .todo, prop := ``NewGenericFields, thm := none },
  { id := "iocov-iobuffer-generic-constructors", juliaFile := "base/iobuffer.jl",
    juliaFns := ["GenericIOBuffer{T}", "GenericIOBuffer"],
    statement := "Generic constructors enforce maxsize, initialize the buffer, and apply truncation.", source := "base/iobuffer.jl:110-137",
    status := .todo, prop := ``GenericConstructors, thm := none },
  { id := "iocov-iobuffer-vector-constructor", juliaFile := "base/iobuffer.jl",
    juliaFns := ["GenericIOBuffer(::Vector{UInt8},...)"],
    statement := "The Vector constructor preserves its memory offset and restricts size to the vector view.", source := "base/iobuffer.jl:141-161",
    status := .todo, prop := ``VectorConstructor, thm := none },
  { id := "iocov-iobuffer-offset-accessors", juliaFile := "base/iobuffer.jl",
    juliaFns := ["get_offset", "get_compacted"],
    statement := "Offset and compacted byte counts are the positive and negative parts of the shared field.", source := "base/iobuffer.jl:163-164",
    status := .todo, prop := ``OffsetAccessors, thm := none },
  { id := "iocov-iobuffer-string-allocators", juliaFile := "base/iobuffer.jl",
    juliaFns := ["StringMemory", "StringVector"],
    statement := "StringVector wraps the storage returned by StringMemory at the requested size.", source := "base/iobuffer.jl:167-168",
    status := .todo, prop := ``StringAllocators, thm := none },
  { id := "iocov-iobuffer-public-constructors", juliaFile := "base/iobuffer.jl",
    juliaFns := ["IOBuffer", "PipeBuffer"],
    statement := "Public constructors apply open flags and the documented readable, writable, seekable, and append settings.", source := "base/iobuffer.jl:230-285",
    status := .todo, prop := ``PublicConstructors, thm := none },
  { id := "iocov-iobuffer-truncated-pipe", juliaFile := "base/iobuffer.jl",
    juliaFns := ["_truncated_pipebuffer"],
    statement := "The internal truncated pipe has no readable bytes, reports EOF, and retains its requested maxsize.", source := "base/iobuffer.jl:289-294",
    status := .todo, prop := ``TruncatedPipeCorrect, thm := none },
  { id := "iocov-iobuffer-similar-data", juliaFile := "base/iobuffer.jl",
    juliaFns := ["_similar_data(::IOBuffer,::Int)"],
    statement := "IOBuffer similar storage is StringMemory of the requested length.", source := "base/iobuffer.jl:297",
    status := .todo, prop := ``SimilarDataCorrect, thm := none },
  { id := "iocov-iobuffer-copy", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copy(::GenericIOBuffer)"],
    statement := "Copy preserves readable buffer storage and position, and compacts owned writable storage.", source := "base/iobuffer.jl:302-332",
    status := .todo, prop := ``CopyReadonlyFields, thm := none },
  { id := "iocov-iobuffer-not-readable", juliaFile := "base/iobuffer.jl",
    juliaFns := ["_throw_not_readable", "read(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::Type{UInt8})"],
    statement := "The unreadable helper always throws the documented ArgumentError, which byte reads and peeks propagate.", source := "base/iobuffer.jl:344-350,438-456",
    status := .todo, prop := ``ThrowNotReadable, thm := none },
  { id := "iocov-iobuffer-unsafe-read-bodies", juliaFile := "base/iobuffer.jl",
    juliaFns := ["unsafe_read!(::Ptr,::AbstractVector,...)", "unsafe_read!(::Ptr,::DenseBytes,...)"],
    statement := "Both unsafe_read! overloads copy exactly the requested consecutive bytes.", source := "base/iobuffer.jl:361-378",
    status := .todo, prop := ``UnsafeReadMethods, thm := none },
  { id := "iocov-iobuffer-load-array", juliaFile := "base/iobuffer.jl",
    juliaFns := ["load_from_array"],
    statement := "load_from_array assembles the requested bytes in little-endian order.", source := "base/iobuffer.jl:394-404",
    status := .todo, prop := ``LoadFromArrayLittleEndian, thm := none },
  { id := "iocov-iobuffer-peek-multibyte", juliaFile := "base/iobuffer.jl",
    juliaFns := ["peek(::GenericIOBuffer,::MultiByteBitNumberType)"],
    statement := "Both multibyte peek paths check readability and availability and do not advance the pointer.", source := "base/iobuffer.jl:406-430",
    status := .todo, prop := ``PeekMethodsDoNotAdvance, thm := none },
  { id := "iocov-iobuffer-read-multibyte", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer,::MultiByteBitNumberType)"],
    statement := "A successful multibyte read advances by sizeof(T).", source := "base/iobuffer.jl:432-436",
    status := .todo, prop := ``ReadMultiAdvances, thm := none },
  { id := "iocov-iobuffer-read-ptr", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer,::Type{Ptr{T}})"],
    statement := "Pointer reads convert the UInt result and preserve the UInt reader's state change.", source := "base/iobuffer.jl:458",
    status := .todo, prop := ``PtrReadIsUIntRead, thm := none },
  { id := "iocov-iobuffer-read-write-flags", juliaFile := "base/iobuffer.jl",
    juliaFns := ["isreadable", "iswritable", "closewrite"],
    statement := "Capability queries match their fields; closewrite clears writability and leaves readability unchanged.", source := "base/iobuffer.jl:460-461,693-696",
    status := .todo, prop := ``ReadWriteFlags, thm := none },
  { id := "iocov-iobuffer-seek-methods", juliaFile := "base/iobuffer.jl",
    juliaFns := ["skip(::GenericIOBuffer,::Int)", "translate_seek_position", "seek(::GenericIOBuffer,::Int)", "seekend"],
    statement := "Seeking methods clamp positions and preserve the documented non-seekable checks.", source := "base/iobuffer.jl:479-529",
    status := .todo, prop := ``SeekMethodsCorrect, thm := none },
  { id := "iocov-iobuffer-ensure-room", juliaFile := "base/iobuffer.jl",
    juliaFns := ["ensureroom", "ensureroom_reallocate"],
    statement := "Room management converts Int to UInt, checks writability, and reallocates or uses the fast path.", source := "base/iobuffer.jl:597-624",
    status := .todo, prop := ``EnsureRoomMethods, thm := none },
  { id := "iocov-iobuffer-close-method", juliaFile := "base/iobuffer.jl",
    juliaFns := ["close(::GenericIOBuffer)"],
    statement := "close releases writable storage and resets every observable buffer field.", source := "base/iobuffer.jl:698-711",
    status := .todo, prop := ``CloseMethodCorrect, thm := none },
  { id := "iocov-iobuffer-isopen-method", juliaFile := "base/iobuffer.jl",
    juliaFns := ["isopen(::GenericIOBuffer)", "close(::GenericIOBuffer)", "closewrite(::GenericIOBuffer)"],
    statement := "A buffer is open when any capability remains or unread bytes remain; close and closewrite update that state accordingly.", source := "base/iobuffer.jl:698-713",
    status := .todo, prop := ``IsopenCorrect, thm := none },
  { id := "iocov-iobuffer-take-methods", juliaFile := "base/iobuffer.jl",
    juliaFns := ["take!(::GenericIOBuffer)", "takestring!(::GenericIOBuffer)"],
    statement := "Generic take returns reachable contents and resets writable buffers; generic takestring converts that result.", source := "base/iobuffer.jl:731-753,862",
    status := .todo, prop := ``TakeMethodsCorrect, thm := none },
  { id := "iocov-iobuffer-unsafe-take", juliaFile := "base/iobuffer.jl",
    juliaFns := ["unsafe_takestring!", "_unsafe_take!"],
    statement := "Unsafe take methods return the used span without resetting the buffer.", source := "base/iobuffer.jl:795-809,876-884",
    status := .todo, prop := ``UnsafeTakeReturnsUsed, thm := none },
  { id := "iocov-iobuffer-write-from-buffer", juliaFile := "base/iobuffer.jl",
    juliaFns := ["write(::IO,::GenericIOBuffer)"],
    statement := "Writing a buffer consumes all readable bytes and rejects self-copy.", source := "base/iobuffer.jl:886-897",
    status := .todo, prop := ``WriteFromConsumes, thm := none },
  { id := "iocov-iobuffer-unsafe-write-bodies", juliaFile := "base/iobuffer.jl",
    juliaFns := ["_unsafe_write(::AbstractVector,...)", "_unsafe_write(::MutableDenseArrayType,...)"],
    statement := "Both low-level write methods store exactly the supplied bytes from the requested index.", source := "base/iobuffer.jl:923-946",
    status := .todo, prop := ``UnsafeWriteMethods, thm := none },
  { id := "iocov-iobuffer-byte-read-write", juliaFile := "base/iobuffer.jl",
    juliaFns := ["write(::GenericIOBuffer,::UInt8)", "readbytes!", "readavailable", "read(::GenericIOBuffer,::Integer)"],
    statement := "Byte I/O methods use the differential-tested state operations and consume no more than available data.", source := "base/iobuffer.jl:948-982",
    status := .todo, prop := ``ByteReadWriteMethods, thm := none },
  { id := "iocov-iobuffer-copyline-methods", juliaFile := "base/iobuffer.jl",
    juliaFns := ["copyline(::GenericIOBuffer,::IO)", "copyline(::IO,::GenericIOBuffer)", "copyline(::GenericIOBuffer,::GenericIOBuffer)"],
    statement := "The optimized copyline methods copy one line, strip the delimiter when requested, and advance the input.", source := "base/iobuffer.jl:1010-1080",
    status := .todo, prop := ``CopylineMethods, thm := none },
  { id := "iocov-iobuffer-crc32c", juliaFile := "base/iobuffer.jl",
    juliaFns := ["_crc32c(::IOBuffer,::Integer,::UInt32)", "_crc32c(::IOBuffer,::UInt32)"],
    statement := "IOBuffer CRC returns the checksum of the available prefix, checks negative counts and unreadable buffers, consumes only that prefix, and defaults to all available bytes.", source := "base/iobuffer.jl:1084-1093",
    status := .todo, prop := ``CrcDefaultUsesAvailable, thm := none },
  { id := "iobuffer-read-available-peek-counts", juliaFile := "base/iobuffer.jl",
    juliaFns := ["readavailable(::GenericIOBuffer)", "read(::GenericIOBuffer, nb::Integer)", "peek(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::MultiByteBitNumberType)"],
    statement := "readavailable returns all unread bytes, read(n) returns min(n, bytesavailable), and peek leaves position unchanged.", source := "base/iobuffer.jl:406-456, 977-982 (read and peek bodies); read and peek contracts",
    status := .todo, prop := ``ReadAvailableAndPeekCounts, thm := none },
  { id := "iobuffer-read-write-permission-errors", juliaFile := "base/iobuffer.jl",
    juliaFns := ["read(::GenericIOBuffer, ::Type{UInt8})", "peek(::GenericIOBuffer, ::Type{UInt8})", "ensureroom_reallocate", "write(::GenericIOBuffer, ::UInt8)", "unsafe_write"],
    statement := "Writes to non-writable buffers and reads from non-readable buffers throw ArgumentError before transferring bytes.", source := "base/iobuffer.jl:344-347, 618-620, 948-963; IOBuffer read/write options",
    status := .todo, prop := ``ReadWritePermissionErrors, thm := none },
  { id := "iobuffer-maxsize-write-cap", juliaFile := "base/iobuffer.jl",
    juliaFns := ["ensureroom", "unsafe_write", "write(::GenericIOBuffer, ::UInt8)"],
    statement := "Every successful write stays within the configured maxsize boundary, including when the backing storage is larger.", source := "base/iobuffer.jl:55-69, 609-610, 910-920, 949-963 (maxsize and write bounds)",
    status := .todo, prop := ``MaxsizeCapsWrites, thm := none },
  { id := "iobuffer-position-bounds", juliaFile := "base/iobuffer.jl",
    juliaFns := ["position", "seek", "seekend", "skip", "mark", "reset", "truncate"],
    statement := "Successful seek, skip, mark/reset and truncate operations keep the zero-based position within the logical buffer size; resetting without a mark throws ArgumentError.", source := "base/iobuffer.jl:69-93, 475-593; mark/reset contracts in base/io.jl",
    status := .todo, prop := ``PositionBoundsAfterOperations, thm := none },
]

end JuliaLean.Proofs.base.iobuffer
