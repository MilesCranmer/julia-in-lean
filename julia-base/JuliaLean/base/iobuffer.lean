import JuliaLean.Core
import JuliaLean.Runtime.Strings
import JuliaLean.base.intfuncs
import JuliaLean.base.pointer
import JuliaLean.base.array
import JuliaLean.base.abstractarray
import JuliaLean.base.genericmemory
import JuliaLean.base.strings.string
import JuliaLean.base.essentials
import JuliaLean.base.number
import JuliaLean.base.some
import JuliaLean.base.io

/-!
Typed model of `base/iobuffer.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

* `data` is the backing vector as a list of bytes; Julia index `k` is list
  index `k - 1`. Freshly allocated memory (`StringMemory`) is uninitialised in
  Julia; its bytes are zero here and are never observable.
* `isMemory` is `T === Memory{UInt8}` (an `IOBuffer`); otherwise the buffer is a
  `GenericIOBuffer` over another vector type such as a `SubArray`, whose
  `similar` is not a `T` and which has no `resize!`.
* The `Int` fields are `JInt64` and use Julia's wrapping arithmetic.
* A mutation made before an exception persists (`EStateM`).
* `IOErr.outOfBounds` marks an `@inbounds`/pointer access outside `data`,
  which Julia does not check (undefined behaviour).
-/

namespace JuliaLean.base.iobuffer

open JuliaLean

/-- Julia `Int`. -/
abbrev I := JInt64
/-- Julia `UInt`. -/
abbrev U := JInt .u64

/-- `x % Int`. -/
def i (x : Int) : I := JInt.wrap .i64 x
/-- `x % UInt`. -/
def u (x : Int) : U := JInt.wrap .u64 x

/-- `typemax(Int)`. -/
def imaxval : I := i (2 ^ 63 - 1)

/-- `max(a, b)` on `Int`. -/
def imax (a b : I) : I := if b.val < a.val then a else b
/-- `min(a, b)` on `Int`. -/
def imin (a b : I) : I := if b.val < a.val then b else a
/-- `min(a, b)` on `UInt`. -/
def uminU (a b : U) : U := if b.val < a.val then b else a
/-- `clamp(x, lo, hi)` on `Int` (`base/intfuncs.jl`): `hi` is tested first. -/
def clampI (x lo hi : I) : I := if x.val > hi.val then hi else if x.val < lo.val then lo else x
/-- `clamp(x, Int)` of a wider integer `x`. -/
def clampToI (x : Int) : I :=
  if x > 2 ^ 63 - 1 then imaxval else if x < -2 ^ 63 then i (-2 ^ 63) else i x

/-- Exceptions thrown by the modelled methods. -/
inductive IOErr where
  | jl (e : JlError)
  | eofError
  | errorException (msg : String)
  | typeError
  /-- An unchecked access outside `data` (undefined behaviour in Julia). -/
  | outOfBounds
  | showError (error : JuliaLean.Strings.ShowErrorKind)
  deriving Repr, DecidableEq, Inhabited
/-- Name of the Julia exception type or retained display-error carrier. -/
def IOErr.name : IOErr → String
  | .jl (.overflowError _) => "OverflowError"
  | .jl (.argumentError _) => "ArgumentError"
  | .jl .boundsError => "BoundsError"
  | .jl (.inexactError _) => "InexactError"
  | .jl .divideError => "DivideError"
  | .jl (.domainError _) => "DomainError"
  | .jl (.methodError _) => "MethodError"
  | .jl .eofError => "EOFError"
  | .eofError => "EOFError"
  | .errorException _ => "ErrorException"
  | .typeError => "TypeError"
  | .outOfBounds => "UB"
  | .showError _ => "ShowError"
/-- Julia `String` stores bytes and may contain non-UTF-8 data. -/
structure JuliaString where
  bytes : List UInt8
  deriving DecidableEq

/-- The fields of `GenericIOBuffer`, `base/iobuffer.jl:33-93`. `offset` is
`offset_or_compacted`. -/
structure BufferState where
  data : List UInt8
  isMemory : Bool
  reinit : Bool
  readable : Bool
  writable : Bool
  seekable : Bool
  append : Bool
  size : I
  maxsize : I
  ptr : I
  offset : I
  mark : I
  deriving DecidableEq

/-- Mutating methods on an `IOBuffer`. -/
abbrev M := EStateM IOErr BufferState

def lift {α} : Except IOErr α → M α
  | .ok a => pure a
  | .error e => throw e

def throwArg {α} (msg : String) : M α := throw (.jl (.argumentError msg))

/-- `convert(Int, x)` / `Int(x)`. -/
def toI (x : Int) : Except IOErr I :=
  match JInt.convert (IntTy.i64.name) .i64 x with
  | .ok v => .ok v
  | .error e => .error (.jl e)

/-- `convert(UInt, x)`. -/
def toU (x : Int) : Except IOErr U :=
  match JInt.convert (IntTy.u64.name) .u64 x with
  | .ok v => .ok v
  | .error e => .error (.jl e)

/-! ## Memory primitives -/

/-- `data[a:b]` (1-based, inclusive) when `1 ≤ a` and `b ≤ length(data)`. -/
def slice (d : List UInt8) (a b : Int) : List UInt8 :=
  (d.drop (a - 1).toNat).take (b - a + 1).toNat

/-- Checked `data[k]`. -/
def getChecked (d : List UInt8) (k : I) : Except IOErr UInt8 :=
  if 1 ≤ k.val ∧ k.val ≤ d.length then .ok (d.getD (k.val - 1).toNat 0) else .error (.jl .boundsError)
 
/- `@inbounds` access is defined only when the pointer is inside the backing bytes. -/
def getUnchecked (d : List UInt8) (k : I) : Except IOErr UInt8 :=
  if 1 ≤ k.val ∧ k.val ≤ d.length then .ok (d.getD (k.val - 1).toNat 0) else .error .outOfBounds

/-- Checked `data[k] = b`. -/
def setChecked (d : List UInt8) (k : I) (b : UInt8) : Except IOErr (List UInt8) :=
  if 1 ≤ k.val ∧ k.val ≤ d.length then .ok (d.set (k.val - 1).toNat b) else .error (.jl .boundsError)

/-- `copyto!(dest, doffs, src, soffs, n)` (`base/genericmemory.jl:266`, `base/array.jl`):
`n == 0` returns, a negative `n` is an `ArgumentError`, out-of-range ranges a `BoundsError`. -/
def copyto (dest : List UInt8) (doffs : I) (src : List UInt8) (soffs n : I) : Except IOErr (List UInt8) :=
  if n.val = 0 then .ok dest
  else if n.val < 0 then .error (.jl (.argumentError "tried to copy n=" ))
  else if 1 ≤ doffs.val ∧ doffs.val + n.val - 1 ≤ dest.length ∧ 1 ≤ soffs.val ∧ soffs.val + n.val - 1 ≤ src.length then
    .ok (dest.take (doffs.val - 1).toNat ++ slice src soffs.val (soffs.val + n.val - 1) ++
      dest.drop (doffs.val - 1 + n.val).toNat)
  else .error (.jl .boundsError)

/-- Write `bs` at index `k` onwards: `_unsafe_write`, `base/iobuffer.jl:923-946`. Memory
data is written through a pointer (unchecked); other vectors use checked `setindex!`. -/
def writeAt (isMemory : Bool) (d : List UInt8) (k : I) (bs : List UInt8) : Except IOErr (List UInt8) :=
  if bs.length = 0 then .ok d
  else if 1 ≤ k.val ∧ k.val + bs.length - 1 ≤ d.length then
    .ok (d.take (k.val - 1).toNat ++ bs ++ d.drop (k.val - 1 + bs.length).toNat)
  else if isMemory then .error .outOfBounds else .error (.jl .boundsError)

/-- Read `n` bytes from index `k` (pointer copy, `unsafe_read!`, `base/iobuffer.jl:361-378`). -/
def readAt (d : List UInt8) (k : I) (n : Nat) : Except IOErr (List UInt8) :=
  if n = 0 then .ok []
  else if 1 ≤ k.val ∧ k.val + n - 1 ≤ d.length then .ok (slice d k.val (k.val + n - 1))
  else .error .outOfBounds

/-- `fill!(view(data, a:b), 0x00)`. -/
def fillZero (d : List UInt8) (a b : I) : Except IOErr (List UInt8) :=
  if b.val < a.val then .ok d
  else if 1 ≤ a.val ∧ b.val ≤ d.length then
    .ok (d.take (a.val - 1).toNat ++ List.replicate (b.val - a.val + 1).toNat 0 ++ d.drop b.val.toNat)
  else .error (.jl .boundsError)

/-- `length(a:b)` for a `UnitRange{Int}`. -/
def rangeLength (a b : I) : I := if b.val < a.val then i 0 else b - a + i 1

/-- `StringMemory(n)`, `base/iobuffer.jl:167`: `_string_n` converts `n` to `Csize_t`. -/
def stringMemory (n : I) : Except IOErr (List UInt8) :=
  if n.val < 0 then .error (.jl (.inexactError "convert")) else .ok (List.replicate n.val.toNat 0)

/-- Number of significant bits of `n`, i.e. `64 - ctlz_int(n)` for `0 ≤ n < 2^64`. -/
def bitLength : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitLength fuel (n / 2) + 1

/-- `overallocation(maxsize)`, `base/array.jl:1102-1112`; a negative argument has no
leading zeros. -/
def overallocation (n : I) : I :=
  let exp2 : Nat := if n.val < 0 then 64 else bitLength 64 n.val.toNat
  let extra := i (2 ^ (exp2 * 7 / 8)) * i 3 + i (n.val.tdiv 8)
  if n.val > (imaxval - extra).val then imaxval else n + extra

/-! ## Field accessors, `base/iobuffer.jl` -/

/-- `get_offset`, `base/iobuffer.jl:163`. -/
def getOffset (io : BufferState) : I := imax (i 0) io.offset
/-- `get_compacted`, `base/iobuffer.jl:164`. -/
def getCompacted (io : BufferState) : I := imax (i 0) (-io.offset)
/-- `bytesavailable`, `base/iobuffer.jl:467`. -/
def bytesavailable (io : BufferState) : I := io.size - io.ptr + i 1
/-- `position`, `base/iobuffer.jl:470-473`. -/
def position (io : BufferState) : I := io.ptr - io.offset - i 1


/-- The virtual size is `size - offset`; a negative offset records bytes removed by compaction. -/
def logicalSize (io : BufferState) : I := io.size - io.offset

def stateInvariant (io : BufferState) : Prop :=
  0 ≤ io.size.val ∧ io.size.val ≤ io.data.length ∧ 0 ≤ io.maxsize.val ∧
  getOffset io ≤ io.size ∧ io.ptr ≥ getOffset io + i 1 ∧ io.ptr ≤ io.size + i 1 ∧
  io.mark.val ≥ -1 ∧ (io.mark.val ≥ 0 → io.mark.val ≤ (logicalSize io).val) ∧
  0 ≤ (position io).val ∧ (position io).val ≤ (logicalSize io).val ∧
  (io.reinit → io.size = i 0 ∧ io.ptr = i 1 ∧ io.offset = i 0)
/-- `filesize`, `base/iobuffer.jl:464`. -/
def filesize (io : BufferState) : I := if io.seekable then io.size - getOffset io else bytesavailable io
/-- `eof`, `base/iobuffer.jl:691`. -/
def eof (io : BufferState) : Bool := decide ((io.ptr - i 1).val ≥ io.size.val)
/-- `ismarked`, `base/io.jl:1615`. -/
def ismarked (io : BufferState) : Bool := decide (io.mark.val ≥ 0)

/-- `translate_seek_position`, `base/iobuffer.jl:500-510`. -/
def translateSeekPosition (io : BufferState) (n : I) : I := clampToI (n.val + io.offset.val + 1)

/-- `get_used_span`, `base/iobuffer.jl:662-673`; defined only for `IOBuffer`. -/
def getUsedSpan (io : BufferState) : Except IOErr (I × I) :=
  if !io.isMemory then .error (.jl (.methodError "get_used_span"))
  else if io.seekable then .ok (getOffset io + i 1, io.size)
  else if io.mark.val > -1 then .ok (imin io.ptr (translateSeekPosition io io.mark), io.size)
  else .ok (io.ptr, io.size)

/-- `_similar_data`, `base/iobuffer.jl:296-297`: `StringMemory` for an `IOBuffer`; for other
vector types `similar` returns a `Vector`, which cannot be stored in the `data::T` field. -/
def similarData (io : BufferState) (n : I) : Except IOErr (List UInt8) :=
  if io.isMemory then stringMemory n else .error (.jl (.methodError "convert"))

/-! ## Constructors -/

/-- A `Vector{UInt8}`: its memory, `memoryrefoffset(ref) - 1`, and its length. -/
structure Vec where
  mem : List UInt8
  off : Nat
  len : Nat
  deriving DecidableEq

/-- The `data` argument of the constructors. -/
inductive DataArg where
  | vec (v : Vec)
  | mem (m : List UInt8)
  /-- A non-`Memory` `AbstractVector{UInt8}` with one-based indexing (e.g. a `view`). -/
  | other (d : List UInt8)
  deriving DecidableEq

/-- Bytes selected by a constructor argument. -/
def dataBytes : DataArg → List UInt8
  | .vec v => (v.mem.drop v.off).take v.len
  | .mem d => d
  | .other d => d

def dataIsMemory : DataArg → Bool
  | .mem _ => true
  | _ => false


def MemoryLengthValid7 (length : Nat) : Prop := (length : Int) < 2 ^ 63 - 1

def VecValid7 (v : Vec) : Prop :=
  MemoryLengthValid7 v.mem.length ∧ v.off + v.len ≤ v.mem.length

def DataValid7 : DataArg → Prop
  | .mem bytes => MemoryLengthValid7 bytes.length
  | .vec vector => VecValid7 vector
  | .other _ => True

def DocumentedInvariant7 (io : BufferState) : Prop :=
  (io.isMemory = true → MemoryLengthValid7 io.data.length) ∧
  0 ≤ io.size.val ∧ io.size.val ≤ io.data.length ∧
  0 ≤ io.maxsize.val ∧
  0 ≤ (getOffset io).val ∧ (getOffset io).val ≤ io.size.val ∧
  (getOffset io).val + 1 ≤ io.ptr.val ∧ io.ptr.val ≤ io.size.val + 1 ∧
  io.size.val - (getOffset io).val ≤ io.maxsize.val ∧
  (io.seekable = true → 0 ≤ io.offset.val) ∧
  -1 ≤ io.mark.val ∧
  (0 ≤ io.mark.val →
    (getOffset io).val ≤ io.mark.val + io.offset.val ∧
    io.mark.val + io.offset.val ≤ io.size.val) ∧
  (io.seekable = false → io.writable = true →
    io.readable = true ∧ io.append = true) ∧
  (io.reinit = true → io.size = i 0 ∧ io.ptr = i 1 ∧ io.offset = i 0)

/-- `open_flags` result. -/
structure Flags where
  read : Bool
  write : Bool
  create : Bool
  truncate : Bool
  append : Bool

/-- `open_flags`, `base/io.jl:401-427`. -/
def openFlags (read write create truncate append : Option Bool) : Flags :=
  let (create, truncate) :=
    if write = some true ∧ read ≠ some true ∧ append ≠ some true then
      (if create.isNone then some true else create, if truncate.isNone then some true else truncate)
    else (create, truncate)
  let (write, create) :=
    if truncate = some true ∨ append = some true then
      (if write.isNone then some true else write, if create.isNone then some true else create)
    else (write, create)
  let write := write.getD false
  { read := read.getD (!write), write, create := create.getD false,
    truncate := truncate.getD false, append := append.getD false }

/-- `_new_generic_iobuffer`, `base/iobuffer.jl:96-107`. -/
def newBuf (data : List UInt8) (isMemory readable writable seekable append : Bool) (maxsize : I) : BufferState :=
  { data, isMemory, reinit := false, readable, writable, seekable, append, size := i data.length,
    maxsize, ptr := i 1, offset := i 0, mark := i (-1) }

/-- `GenericIOBuffer(data, readable, writable, seekable, append, maxsize, truncate)`:
`base/iobuffer.jl:110-130` for `Memory`/other vectors, `141-161` for a `Vector`. -/
def genericIOBuffer (data : DataArg) (readable writable seekable append : Bool) (maxsize : Int)
    (truncate : Bool) : Except IOErr BufferState := do
  match data with
  | .vec v =>
    let mz ← toI maxsize
    if !truncate ∧ mz.val < v.len then .error (.jl (.argumentError "maxsize must not be smaller than data length"))
    let buf := newBuf v.mem true readable writable seekable append mz
    let buf := { buf with offset := i v.off, ptr := i (v.off + 1) }
    pure { buf with size := if truncate then i v.off else i (v.len + v.off) }
  | .mem d | .other d =>
    let mz ← toI maxsize
    if !truncate ∧ mz.val < d.length then .error (.jl (.argumentError "maxsize must not be smaller than data length"))
    let buf := newBuf d (match data with | .mem _ => true | _ => false) readable writable seekable append mz
    pure (if truncate then { buf with size := buf.offset } else buf)


/-! ## Buffer management -/

/-- `compact!`, `base/iobuffer.jl:677-689`. -/
def compact : M I := do
  let io ← get
  let offset := getOffset io
  let (a, b) ← lift (getUsedSpan io)
  let deleted := a - i 1
  let compacted := deleted - offset
  if deleted.val = 0 then return i 0
  let data ← lift (copyto io.data (i 1) io.data (deleted + i 1) (rangeLength a b))
  set { io with data, offset := -getCompacted io - compacted, ptr := io.ptr - deleted,
                size := io.size - deleted }
  return deleted

/-- `_resize!`, `base/iobuffer.jl:536-556`; neither `Memory` nor the other modelled vector
types support `resize!`. -/
def resize (newSize : I) (exact : Bool) : M Unit := do
  let io ← get
  let oldData := io.data
  let newSize := if exact then newSize else imin io.maxsize (overallocation newSize)
  let (a, b) ← lift (getUsedSpan io)
  let deleted := a - i 1
  let compacted := deleted - getOffset io
  let newData ← lift (similarData io newSize)
  set { io with data := newData }
  if newSize.val = 0 then return
  let lenUsed := rangeLength a b
  let newData ← if lenUsed.val = 0 then pure newData else lift (copyto newData (i 1) oldData a lenUsed)
  set { io with data := newData, offset := -getCompacted io - compacted, ptr := io.ptr - deleted,
                size := lenUsed }

/-- `ensureroom_reallocate`, `base/iobuffer.jl:618-624`. -/
def ensureroomReallocate (nshort : U) : M Unit := do
  let io ← get
  if !io.writable then throwArg "ensureroom failed, IOBuffer is not writeable"
  let d ← lift (similarData io (imin io.maxsize (JInt.rem .i64 nshort)))
  set { io with data := d, reinit := false, offset := -getCompacted io }

/-- `ensureroom_slowpath`, `base/iobuffer.jl:627-659`. -/
def ensureroomSlowpath (nshort : U) (available : I) : M Unit := do
  let io ← get
  let (a, _) ← lift (getUsedSpan io)
  let reclaimable := a - i 1
  if reclaimable.val ≥ 32 ∧ reclaimable.val ≥ (io.data.length / 8 : Nat) ∧
      (JInt.rem .u64 (reclaimable + available)).val ≥ nshort.val then
    let _ ← compact
    return
  let n ← lift (toI nshort.val)
  let desired := i io.data.length + n - available
  if desired.val > io.maxsize.val then
    if reclaimable.val ≠ 0 then
      discard compact
    let io ← get
    if io.data.length < io.maxsize.val then resize io.maxsize true
  else
    resize desired false

/-- `ensureroom(io, nshort::UInt)`, `base/iobuffer.jl:599-615`. -/
def ensureroom (nshort : U) : M Unit := do
  let io ← get
  if !io.writable || io.reinit then ensureroomReallocate nshort
  else
    let start := if io.append then io.size else io.ptr - i 1
    let existing := imin (i io.data.length - start) (io.maxsize - (start - getOffset io))
    if existing.val < (JInt.rem .i64 nshort).val then ensureroomSlowpath nshort existing

/-! ## Writing -/

/-- `unsafe_write(to, p, nb)` with `p` pointing at `src`, `base/iobuffer.jl:902-921`;
`write(io, ::Vector{UInt8})` calls it. -/
def unsafeWrite (src : List UInt8) : M I := do
  let nb : U := u src.length
  ensureroom nb
  let io ← get
  let size := io.size
  let append := io.append
  let ptr := if append then size + i 1 else io.ptr
  let start := ptr - i 1
  let inner := imin (i io.data.length - start) (io.maxsize - (start - getOffset io))
  let toWrite := imax (i 0) (JInt.rem .i64 (uminU nb (JInt.rem .u64 inner)))
  let data ← lift (writeAt io.isMemory io.data ptr (src.take toWrite.val.toNat))
  set { io with data, size := imax size (start + toWrite),
                ptr := if append then io.ptr else ptr + toWrite }
  return toWrite

/-- `write(to, a::UInt8)`, `base/iobuffer.jl:948-963`. -/
def writeByte (a : UInt8) : M I := do
  ensureroom (u 1)
  let io ← get
  let ptr := if io.append then io.size + i 1 else io.ptr
  if (ptr - getOffset io).val > io.maxsize.val then return i 0
  let data ← lift (setChecked io.data ptr a)
  set { io with data, size := imax io.size ptr, ptr := if io.append then io.ptr else io.ptr + i 1 }
  return i 1

/-! ## Reading -/

def throwNotReadable {α} : M α := throwArg "read failed, IOBuffer is not readable"

/-- `read(from, UInt8)`, `base/iobuffer.jl:438-448`. -/
def readByte : M UInt8 := do
  let io ← get
  if !io.readable then throwNotReadable
  if io.ptr.val > io.size.val then throw .eofError
  let b ← lift (readAt io.data io.ptr 1)
  set { io with ptr := io.ptr + i 1 }
  return b.headD 0

/-- `peek(from, UInt8)`, `base/iobuffer.jl:450-456`. -/
def peekByte : M UInt8 := do
  let io ← get
  if !io.readable then throwNotReadable
  if io.ptr.val > io.size.val then throw .eofError
  lift (getChecked io.data io.ptr)

/-- `unsafe_read(from, p, nb)`, `base/iobuffer.jl:349-359`: the bytes stored at `p`. -/
def unsafeRead (nb : U) : M (List UInt8) := do
  let io ← get
  if !io.readable then throwNotReadable
  let avail := JInt.rem .u64 (bytesavailable io)
  let adv := uminU avail nb
  let bytes ← lift (readAt io.data io.ptr adv.val.toNat)
  let np ← lift (toI (JInt.rem .u64 io.ptr + adv).val)
  set { io with ptr := np }
  if nb.val > avail.val then throw .eofError
  return bytes

/-- `read!(io, A)` for `A::Vector{UInt8}` of length `n` (`base/io.jl:1019-1022, 998`). -/
def readBang (n : Nat) : M (List UInt8) := do
  let nb ← lift (toU n)
  unsafeRead nb

/-- `peek(from, T)` for an `nb`-byte bits type `T`, `base/iobuffer.jl:418-430`: its
little-endian bytes. -/
def peekT (nb : Nat) : M (List UInt8) := do
  let io ← get
  if !io.readable then throwNotReadable
  if (nb : Int) > (bytesavailable io).val then throw .eofError
  lift (readAt io.data io.ptr nb)

/-- `read(from, T)` for an `nb`-byte bits type `T`, `base/iobuffer.jl:432-436`. -/
def readT (nb : Nat) : M (List UInt8) := do
  let x ← peekT nb
  modify fun io => { io with ptr := io.ptr + i nb }
  return x

/-! ## Seeking and marks -/

/-- `seek(io, n::Int)`, `base/iobuffer.jl:512-524`. -/
def seek (n : I) : M Unit := do
  let io ← get
  if !io.seekable then
    if !ismarked io then throwArg "seek failed, IOBuffer is not seekable and is not marked"
    if n ≠ io.mark then throwArg "seek failed, IOBuffer is not seekable and n != mark"
  let maxPtr := io.size + i 1
  let minPtr := getOffset io + i 1
  set { io with ptr := clampI (translateSeekPosition io n) minPtr maxPtr }

/-- `seek(io, n::Integer)`, `base/iobuffer.jl:496-498`. -/
def seekAny (n : Int) : M Unit := seek (clampToI n)

/-- `seekstart`, `base/iostream.jl:185`. -/
def seekstart : M Unit := seek (i 0)

/-- `seekend`, `base/iobuffer.jl:526-529`. -/
def seekend : M Unit := modify fun io => { io with ptr := io.size + i 1 }

/-- `skip(io, n::Integer)`, `base/iobuffer.jl:475-494`. -/
def skip (n : Int) : M Unit := do
  let n := clampToI n
  if n.val < 0 then
    let io ← get
    seek (clampToI ((position io).val + n.val))
  else
    let io ← get
    let nmax := io.size + i 1 - io.ptr
    set { io with ptr := io.ptr + imin n nmax }

/-- `mark`, `base/io.jl:1575-1577`. -/
def mark : M I := do
  let io ← get
  set { io with mark := position io }
  return position io

/-- `unmark`, `base/io.jl:1586-1590`. -/
def unmark : M Bool := do
  let io ← get
  if !ismarked io then return false
  set { io with mark := i (-1) }
  return true

/-- `reset`, `base/io.jl:1600-1606`. -/
def reset : M I := do
  let io ← get
  if !ismarked io then throwArg "IOBuffer not marked"
  let m := io.mark
  seek m
  modify fun io => { io with mark := i (-1) }
  return m

/-! ## Truncation and taking -/

/-- `truncate(io, n::Int)`, `base/iobuffer.jl:558-593`. -/
def truncate (n : I) : M Unit := do
  let io ← get
  if !io.writable then throwArg "truncate failed, IOBuffer is not writeable"
  if !io.seekable then throwArg "truncate failed, IOBuffer is not seekable"
  if n.val < 0 then throwArg "truncate failed, n bytes must be ≥ 0"
  if n.val > io.maxsize.val then throwArg "truncate failed, n bytes exceeds IOBuffer maxsize"
  let offset := getOffset io
  let currentSize := io.size - offset
  if io.reinit then
    let d ← lift (similarData io n)
    set { io with data := List.replicate d.length 0, reinit := false, size := n }
  else if n.val < currentSize.val then
    let io := if (translateSeekPosition io io.mark).val > (n + offset).val then { io with mark := i (-1) } else io
    set { io with size := n + offset, ptr := imin io.ptr (n + offset + i 1) }
  else if n.val > currentSize.val then
    if (n + offset).val > io.maxsize.val then
      discard compact
    resize (n + getOffset (← get)) false
    let io ← get
    let hi := imin (i io.data.length) (n + getOffset io)
    let data ← lift (fillZero io.data (io.size + i 1) hi)
    set { io with data, size := hi }

/-- The reset at the end of `take!`/`takestring!` for a writable buffer. -/
def resetTaken (io : BufferState) : BufferState := { io with reinit := true, ptr := i 1, size := i 0, offset := i 0 }

/-- `wrap(Array, memoryref(data, k), n)`: the `n` bytes from index `k`. -/
def wrapBytes (d : List UInt8) (k n : I) : Except IOErr (List UInt8) :=
  if 1 ≤ k.val ∧ k.val + n.val - 1 ≤ d.length then .ok (slice d k.val (k.val + n.val - 1))
  else .error (.jl .boundsError)

/-- `take!`: `base/iobuffer.jl:758-786` for an `IOBuffer`, `731-753` otherwise. -/
def take : M (List UInt8) := do
  modify fun io => { io with mark := i (-1) }
  let io ← get
  let data ←
    if io.isMemory then
      if io.seekable then
        let nbytes := filesize io
        if nbytes.val = 0 ∨ io.reinit then pure []
        else lift (wrapBytes io.data (getOffset io + i 1) nbytes)
      else
        let nbytes := bytesavailable io
        if nbytes.val = 0 then pure []
        else if io.writable then lift (wrapBytes io.data io.ptr nbytes)
        else throw (.errorException "Unreachable IOBuffer state")
    else
      if io.seekable then
        let offset := getOffset io
        let nbytes := io.size - offset
        let d ← lift (stringMemory nbytes)
        lift (copyto d (i 1) io.data (offset + i 1) nbytes)
      else
        let d ← lift (stringMemory (bytesavailable io))
        readBang d.length
  let io ← get
  if io.writable then set (resetTaken io)
  return data

/-- `takestring!`, `base/iobuffer.jl:795-862`: the bytes of the returned `String`. -/
def takestring : M (List UInt8) := do
  let io ← get
  if !io.isMemory then
    let r ← take
    return r
  if io.reinit then return []
  if io.writable then
    let (a, b) ← lift (getUsedSpan io)
    let s := if (rangeLength a b).val = 0 then [] else slice io.data a.val b.val
    set { resetTaken io with mark := i (-1) }
    return s
  else
    let (a, b) ← lift (getUsedSpan io)
    return slice io.data a.val b.val

/-! ## Delimited reading -/

/-- `view(io.data, io.ptr:io.size)`. -/
def pending (io : BufferState) : Except IOErr (List UInt8) :=
  if io.size.val < io.ptr.val then .ok []
  else if 1 ≤ io.ptr.val ∧ io.size.val ≤ io.data.length then .ok (slice io.data io.ptr.val io.size.val)
  else .error (.jl .boundsError)

/-- `something(findfirst(==(delim), d), length(d))`. -/
def findOrLen (d : List UInt8) (delim : UInt8) : Nat :=
  match d.idxOf? delim with
  | some k => k + 1
  | none => d.length

/-- `readuntil(io, delim::UInt8; keep)`, i.e. `copyuntil(IOBuffer(), io, delim; keep)`,
`base/io.jl:624-626`, `base/iobuffer.jl:993-1008`: the bytes copied. -/
def readuntil (delim : UInt8) (keep : Bool) : M (List UInt8) := do
  let io ← get
  let d ← lift (pending io)
  let nread := findOrLen d delim
  let nout := if !keep ∧ nread > 0 ∧ d.getD (nread - 1) 0 = delim then nread - 1 else nread
  set { io with ptr := io.ptr + i nread }
  return d.take nout

/-- `readline(io; keep)`, i.e. `_copyline(IOBuffer(), io; keep)`, `base/io.jl:714-716`,
`base/iobuffer.jl:1057-1074`: the bytes of the line. -/
def readline (keep : Bool) : M (List UInt8) := do
  let io ← get
  let d ← lift (pending io)
  let nread := findOrLen d 0x0a
  let nout :=
    if !keep ∧ nread > 0 ∧ d.getD (nread - 1) 0 = 0x0a then
      if nread - 1 > 0 ∧ d.getD (nread - 2) 0 = 0x0d then nread - 2 else nread - 1
    else nread
  set { io with ptr := io.ptr + i nread }
  return d.take nout

/-- `occursin(delim::UInt8, buf)`, `base/iobuffer.jl:984-986`. -/
def occursin (delim : UInt8) (io : BufferState) : Except IOErr Bool := do
  let d ← pending io
  pure (d.contains delim)


/-- `peek(s, T)` for a one-byte `T` other than `UInt8` (e.g. `Int8`), the generic method
`base/io.jl:382-388`: `mark`, `read`, then `reset` in a `finally`. -/
def peekGeneric : M UInt8 := do
  let _ ← mark
  let r ← tryCatch readByte (fun e => do let _ ← reset; throw e)
  let _ ← reset
  return r

/-! ## Closing -/

/-- `closewrite`, `base/iobuffer.jl:693-696`. -/
def closewrite : M Unit := modify fun io => { io with writable := false }

/-- The field assignments at the end of `close`, `base/iobuffer.jl:702-709`. -/
def closedState (io : BufferState) : BufferState :=
  { io with readable := false, writable := false, seekable := false, size := i 0,
            maxsize := i 0, ptr := i 1, mark := i (-1), offset := -getCompacted io }

/-- `close`, `base/iobuffer.jl:698-711`. -/
def close : M Unit := do
  let io ← get
  if io.writable ∧ !io.reinit then resize (i 0) true
  modify closedState



/-! ## Verbatim Julia source blocks and typed method models -/

abbrev Byte := JInt .u8

def zero : I := JuliaLean.base.int.lit .i64 0
def one : I := JuliaLean.base.int.lit .i64 1

def liftIO {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {A : Type} :
    Except IOErr A → m A
  | .ok value => pure value
  | .error error => throw error

def liftNative {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {A : Type}
    (value : Jl A) : m A := liftIO (value.mapError IOErr.jl)

structure Fields (D : Type) where
  data : D
  reinit : Bool
  readable : Bool
  writable : Bool
  seekable : Bool
  append : Bool
  size : I
  maxsize : I
  ptr : I
  offset : I
  mark : I
  deriving DecidableEq

structure Access (m : Type → Type) (R D : Type) where
  get : R → m (Fields D)
  set : R → Fields D → m Unit
  new : Fields D → m R
  isIOBuffer : R → m Bool

def bufferFields (io : BufferState) : Fields (List UInt8) where
  data := io.data
  reinit := io.reinit
  readable := io.readable
  writable := io.writable
  seekable := io.seekable
  append := io.append
  size := io.size
  maxsize := io.maxsize
  ptr := io.ptr
  offset := io.offset
  mark := io.mark

def updateBufferFields (io : BufferState) (f : Fields (List UInt8)) : BufferState where
  data := f.data
  isMemory := io.isMemory
  reinit := f.reinit
  readable := f.readable
  writable := f.writable
  seekable := f.seekable
  append := f.append
  size := f.size
  maxsize := f.maxsize
  ptr := f.ptr
  offset := f.offset
  mark := f.mark

def bufferAccess : Access M Unit (List UInt8) where
  get := fun _ => do pure (bufferFields (← get))
  set := fun _ f => modify fun io => updateBufferFields io f
  new := fun f => do
    modify fun io => updateBufferFields io f
    pure ()
  isIOBuffer := fun _ => do pure (← get).isMemory

def ctorStateAccess (isMemory : Bool) :
    Access (StateT BufferState (Except IOErr)) Unit (List UInt8) where
  get := fun _ => do pure (bufferFields (← get))
  set := fun _ f => modify fun io => { updateBufferFields io f with isMemory }
  new := fun f => do
    set { updateBufferFields (← get) f with isMemory }
    pure ()
  isIOBuffer := fun _ => pure isMemory

def fieldsOffset {D : Type} (io : Fields D) : I :=
  JuliaLean.base.int.jmax zero io.offset

def fieldsCompacted {D : Type} (io : Fields D) : I :=
  JuliaLean.base.int.jmax zero (JuliaLean.base.int.neg_int io.offset)

def fieldsPosition {D : Type} (io : Fields D) : I :=
  JuliaLean.base.int.sub (JuliaLean.base.int.sub io.ptr io.offset) one

def fieldsBytesavailable {D : Type} (io : Fields D) : I :=
  JuliaLean.base.int.add (JuliaLean.base.int.sub io.size io.ptr) one

def fieldsIsmarked {D : Type} (io : Fields D) : Bool := decide (io.mark.val ≥ 0)

def fieldsFilesize {D : Type} (io : Fields D) : I :=
  if io.seekable then JuliaLean.base.int.sub io.size (fieldsOffset io) else fieldsBytesavailable io

def clampInteger {N : Type} (gt lt : N → I → Bool) (convert : N → Jl I) (n : N) :
    Except IOErr I :=
  (JuliaLean.base.intfuncs.clamp_Type (JInt.typemin .i64) (JInt.typemax .i64)
    gt lt convert n).mapError IOErr.jl

def clampBits {t : IntTy} (n : JInt t) : Except IOErr I :=
  clampInteger (fun n hi => JuliaLean.base.int.lt hi n)
    (fun n lo => JuliaLean.base.int.lt n lo) (JuliaLean.base.int.convert .i64) n

def intClampgt (n : Int) (hi : I) : Bool := decide (hi.val < n)
def intClamplt (n : Int) (lo : I) : Bool := decide (n < lo.val)
def intClampConvert (n : Int) : Jl I := JInt.convert (IntTy.i64.name) .i64 n

export JuliaLean.base.abstractarray (hasOffsetVector requireOneBased)
export JuliaLean.base.strings.string (stringN unsafeWrapMemory)

inductive Multibyte where
  | u16 | i16 | u32 | i32 | u64 | i64 | u128 | i128 | f16 | f32 | f64

def wordType : Multibyte → IntTy
  | .u16 | .i16 | .f16 => .u16
  | .u32 | .i32 | .f32 => .u32
  | .u64 | .i64 | .f64 => .u64
  | .u128 | .i128 => .u128

def valueType : Multibyte → Type
  | .u16 => JInt .u16 | .i16 => JInt .i16
  | .u32 => JInt .u32 | .i32 => JInt .i32
  | .u64 => JInt .u64 | .i64 => JInt .i64
  | .u128 => JInt .u128 | .i128 => JInt .i128
  | .f16 => JuliaLean.base.float.FV .f16
  | .f32 => JuliaLean.base.float.FV .f32
  | .f64 => JuliaLean.base.float.FV .f64

def initialWord : (kind : Multibyte) → JInt (wordType kind)
  | .u16 => JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .u16 0)
  | .i16 => JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .i16 0)
  | .u32 => JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .u32 0)
  | .i32 => JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .i32 0)
  | .u64 => JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .u64 0)
  | .i64 => JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .i64 0)
  | .u128 => JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .u128 0)
  | .i128 => JuliaLean.base.int.unsigned (JuliaLean.base.int.lit .i128 0)
  | .f16 => JuliaLean.base.int.lit (JuliaLean.base.float.FTy.uintTy .f16) 0
  | .f32 => JuliaLean.base.int.lit (JuliaLean.base.float.FTy.uintTy .f32) 0
  | .f64 => JuliaLean.base.int.lit (JuliaLean.base.float.FTy.uintTy .f64) 0

def bitcastWord : (kind : Multibyte) → JInt (wordType kind) → valueType kind
  | .u16, word => JuliaLean.base.int.bitcast .u16 word rfl
  | .i16, word => JuliaLean.base.int.bitcast .i16 word rfl
  | .u32, word => JuliaLean.base.int.bitcast .u32 word rfl
  | .i32, word => JuliaLean.base.int.bitcast .i32 word rfl
  | .u64, word => JuliaLean.base.int.bitcast .u64 word rfl
  | .i64, word => JuliaLean.base.int.bitcast .i64 word rfl
  | .u128, word => JuliaLean.base.int.bitcast .u128 word rfl
  | .i128, word => JuliaLean.base.int.bitcast .i128 word rfl
  | .f16, word => JuliaLean.base.float.reinterpret_Float_Int .f16 word
  | .f32, word => JuliaLean.base.float.reinterpret_Float_Int .f32 word
  | .f64, word => JuliaLean.base.float.reinterpret_Float_Int .f64 word

def reinterpretWord {m : Type → Type} [Monad m]
    (full : (kind : Multibyte) → JInt (wordType kind) → m (valueType kind))
    (kind : Multibyte) (word : JInt (wordType kind)) : m (valueType kind) :=
  JuliaLean.base.essentials.reinterpret
    (fun _ : Unit => true) (fun _ : JInt (wordType kind) => true)
    (fun _ value => pure (bitcastWord kind value)) (fun _ value => full kind value) () word

structure HeapAccess (m : Type → Type) where
  get : m JuliaLean.base.pointer.ByteHeap
  set : JuliaLean.base.pointer.ByteHeap → m Unit

def pointerConstructor {T : Type} (value : JuliaLean.base.pointer.NativeInt) :
    JuliaLean.base.pointer.Ptr T :=
  ⟨JuliaLean.base.pointer.NativeInt.toUInt64 value⟩

structure CrcCalls (m : Type → Type) (D N Count Sum P : Type) where
  negative : N → m Bool
  showCount : N → m String
  minimum : N → I → m Count
  iszero : Count → m Bool
  pointer : D → I → m P
  unsafeCrc : P → Count → UInt32 → m UInt32
  addPointer : I → Count → m Sum
  toNativePointer : Sum → m I

def crcForeignCall {m : Type → Type} [Monad m] {P Count : Type}
    (toCsize : Count → m U) (runtime : P → U → UInt32 → m UInt32)
    (pointer : P) (count : Count) (seed : UInt32) : m UInt32 := do
  runtime pointer (← toCsize count) seed

local instance (n : Nat) : OfNat U n where
  ofNat := JuliaLean.base.int.lit .u64 n

def iszeroInt {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] (value : I) : m Bool :=
  liftNative (JuliaLean.base.number.iszero
    (fun x => pure (JuliaLean.base.int.zero x))
    (fun x y => pure (JuliaLean.base.int.eq_int x y)) value)

def isoneInt {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] (value : I) : m Bool :=
  liftNative (JuliaLean.base.number.isone
    (JuliaLean.base.number.oneValue (fun _ : I => ())
      (JuliaLean.base.number.oneType
        (fun _ : Unit => fun n => JuliaLean.base.int.convert .i64
          (JuliaLean.base.int.lit .i64 n))))
    (fun x y => pure (JuliaLean.base.int.eq_int x y)) value)

structure Storage (m : Type → Type) (R D NewData : Type) where
  Length : Type
  LastIndex : Type
  IndexDifference : Type
  SpaceOther : Type
  ShiftedLength : Type
  AddedLength : Type
  DesiredOther : Type
  Bound : Type
  length : D → m Length
  lastIndex : D → m LastIndex
  subtractIndex : LastIndex → I → m IndexDifference
  minimumSpace : IndexDifference → I → m (I ⊕ SpaceOther)
  spaceLess : (I ⊕ SpaceOther) → I → m Bool
  shiftLength : Length → m ShiftedLength
  reclaimEnough : I → ShiftedLength → m Bool
  addLength : Length → I → m AddedLength
  subtractAvailable : AddedLength → I → m (I ⊕ DesiredOther)
  desiredGreater : (I ⊕ DesiredOther) → I → m Bool
  lengthLess : Length → I → m Bool
  lengthToInt : Length → m I
  minimumLength : Length → I → m Bound
  boundToInt : Bound → m I
  applicableResize : D → I → m Bool
  resize : D → I → m Unit
  similar : R → I → m NewData
  convertData : NewData → m D
  copyIntoNew : NewData → I → D → I → I → m Unit
  copyWithin : D → I → D → I → I → m Unit
  spanLength : I → I → m I
  fillNew : NewData → Byte → m Unit
  fillView : D → I → Bound → Byte → m Unit

def sourceOverallocation {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] (size : I) : m I :=
  JuliaLean.base.array.overallocation JuliaLean.base.int.ctlz_int
    (fun x y => liftNative (JuliaLean.base.int.divSame x y)) JuliaLean.base.int.shl_Int size

def pointerLoad {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m]
    (h : HeapAccess m) (codec : JuliaLean.base.pointer.ByteCodec Byte)
    (pointer : JuliaLean.base.pointer.Ptr Byte) (index : U) : m Byte := do
  let heap ← h.get
  match JuliaLean.base.pointer.unsafeLoad codec
      (fun n => (JuliaLean.base.int.convert .i64 n).mapError
        JuliaLean.base.pointer.PointerError.julia) pointer heap index with
  | .ok byte => pure byte
  | .error error => throw error

def pointerStore {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m]
    (h : HeapAccess m) (codec : JuliaLean.base.pointer.ByteCodec Byte)
    (pointer : JuliaLean.base.pointer.Ptr Byte) (byte : Byte) (index : U) : m Unit := do
  let heap ← h.get
  match JuliaLean.base.pointer.unsafeStoreTyped codec
      (fun value => (JuliaLean.base.int.convert .u8 value).mapError
        JuliaLean.base.pointer.PointerError.julia)
      (fun n => (JuliaLean.base.int.convert .i64 n).mapError
        JuliaLean.base.pointer.PointerError.julia) pointer heap byte index with
  | .ok (next, _) => h.set next
  | .error error => throw error

def pointerAdvance (pointer : JuliaLean.base.pointer.Ptr Byte) : JuliaLean.base.pointer.Ptr Byte :=
  JuliaLean.base.pointer.ptrAddI64 pointer one

def pointerCopy {m : Type → Type} [Monad m]
    (memmove : JuliaLean.base.pointer.Ptr Byte → JuliaLean.base.pointer.Ptr Byte → U → m Unit)
    (dest src : JuliaLean.base.pointer.Ptr Byte) (count : U) :
    m (JuliaLean.base.pointer.Ptr Byte) :=
  JuliaLean.base.array.unsafeCopyPtr one
    (fun (n : U) (size : I) => JuliaLean.base.int.binop JuliaLean.base.int.mulSame n size)
    memmove dest src count

def arraySet {m : Type → Type} [Monad m] {D Ref : Type}
    (bounds : D → I → m Unit) (memoryrefnew : D → I → Bool → m Ref)
    (memoryrefset : Ref → Byte → Bool → m Unit) (data : D) (byte : Byte) (index : I) : m Unit := do
  let _ ← JuliaLean.base.array.setindexTyped bounds memoryrefnew memoryrefset data byte index
  pure ()

structure StringVectorOps (m : Type → Type) (Vector Ref Memory StringRef : Type) where
  length : Vector → m I
  reference : Vector → m Ref
  ptrOrOffset : Ref → m U
  memory : Ref → m Memory
  memoryPointer : Memory → m U
  memoryToString : Memory → I → m StringRef
  pointerToString : Ref → I → m StringRef
  emptyString : m StringRef
  emptyMemory : m Memory
  memoryref : Memory → m Ref
  setSize : Vector → I → m Unit
  setReference : Vector → Ref → m Unit

def stringVectorConvert {m : Type → Type} [Monad m] {Vector Ref Memory StringRef : Type}
    (s : StringVectorOps m Vector Ref Memory StringRef) (vector : Vector) : m StringRef := do
  let length ← s.length vector
  if JuliaLean.base.int.eq_int length zero then return (← s.emptyString)
  let reference ← s.reference vector
  let pointer ← s.ptrOrOffset reference
  let memory ← s.memory reference
  let base ← s.memoryPointer memory
  let string ← if JuliaLean.base.int.eq_int pointer base then s.memoryToString memory length
    else s.pointerToString reference length
  s.setSize vector zero
  s.setReference vector (← s.memoryref (← s.emptyMemory))
  pure string

inductive ShowArgument where
  | text (value : String)
  | boolean (value : Bool)
  | integer (value : I)

def printArgs {m : Type → Type} [Monad m] {E Out Arg : Type} [MonadExceptOf E m]
    (lock unlock : Out → m Unit) (printOne : Out → Arg → m Unit)
    (out : Out) (arguments : List Arg) : m Unit := do
  lock out
  try
    for argument in arguments do printOne out argument
  catch error =>
    unlock out
    throw error
  unlock out

def somethingResult (found : Option I) (fallback : I) :
    Jl (JuliaLean.base.some.Value I) :=
  JuliaLean.base.some.something
    [match found with
      | none => .nothing
      | some value => .scalar value,
     .scalar fallback]

private theorem somethingResult_scalar (found : Option I) (fallback : I) :
    ∃ value, somethingResult found fallback = .ok (.scalar value) := by
  cases found with
  | none =>
      exact ⟨fallback, by simp [somethingResult, JuliaLean.base.some.something,
        JuliaLean.base.some.somethingNothing, JuliaLean.base.some.somethingAny]⟩
  | some value =>
      exact ⟨value, by simp [somethingResult, JuliaLean.base.some.something,
        JuliaLean.base.some.somethingAny]⟩

def extractSomething (result : Jl (JuliaLean.base.some.Value I))
    (h : ∃ value, result = .ok (.scalar value)) : I :=
  match hresult : result with
  | .ok (.scalar value) => value
  | .ok .nothing => False.elim (by rcases h with ⟨value, h⟩; cases h)
  | .ok (.some _) => False.elim (by rcases h with ⟨value, h⟩; cases h)
  | .error _ => False.elim (by rcases h with ⟨value, h⟩; cases h)

def somethingIndex (found : Option I) (fallback : I) : I :=
  extractSomething (somethingResult found fallback) (somethingResult_scalar found fallback)

/--
Julia source: base/iobuffer.jl:96-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global function _new_generic_iobuffer(
            ::Type{T},
            data::T,
            readable::Bool,
            writable::Bool,
            seekable::Bool,
            append::Bool,
            maxsize::Int,
        ) where T<:AbstractVector{UInt8}
        len = Int(length(data))::Int
        return new{T}(data, false, readable, writable, seekable, append, len, maxsize, 1, 0, -1)
    end
```
-/
def source_new_generic_iobuffer {m : Type → Type} [Monad m] {R D L : Type} (a : Access m R D)
    (length : D → m L) (toIntLength : L → m I) (data : D)
    (readable writable seekable append : Bool) (maxsize : I) : m R := do
  let len ← toIntLength (← length data)
  a.new {
    data := data
    reinit := false
    readable := readable
    writable := writable
    seekable := seekable
    append := append
    size := len
    maxsize := maxsize
    ptr := one
    offset := zero
    mark := JuliaLean.base.int.lit .i64 (-1) }

abbrev newGeneric := @source_new_generic_iobuffer

/--
Julia source: base/iobuffer.jl:110-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function GenericIOBuffer{T}(
        data::T,
        readable::Bool,
        writable::Bool,
        seekable::Bool,
        append::Bool,
        maxsize::Integer,
        truncate::Bool,
    ) where T<:AbstractVector{UInt8}
    require_one_based_indexing(data)
    mz = Int(maxsize)::Int
    len = Int(length(data))::Int
    if !truncate && mz < len
        throw(ArgumentError("maxsize must not be smaller than data length"))
    end
    buf = _new_generic_iobuffer(T, data, readable, writable, seekable, append, mz)
    if truncate
        buf.size = buf.offset_or_compacted
    end
    buf
end
```
-/
def source_GenericIOBuffer_typed {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m] {R D L N : Type}
    (a : Access m R D) (hasOffset : D → m Bool)
    (length : D → m L) (toIntLength : L → m I) (toIntMax : N → m I)
    (data : D) (readable writable seekable append : Bool) (maxsize : N) (truncate : Bool) : m R := do
  let _ ← requireOneBased hasOffset data
  let mz ← toIntMax maxsize
  let len ← toIntLength (← length data)
  if !truncate && JuliaLean.base.int.lt mz len then
    throwThe IOErr (.jl (.argumentError "maxsize must not be smaller than data length"))
  let ref ← source_new_generic_iobuffer a length toIntLength data readable writable seekable append mz
  if truncate then
    let io ← a.get ref
    a.set ref { io with size := io.offset }
  pure ref

abbrev genericConstructor := @source_GenericIOBuffer_typed

def genericConstructorArray {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m] {R D L N : Type}
    (a : Access m R D) (length : D → m L) (toIntLength : L → m I) (toIntMax : N → m I)
    (data : D) (readable writable seekable append : Bool) (maxsize : N) (truncate : Bool) : m R :=
  source_GenericIOBuffer_typed a (fun data => pure (JuliaLean.base.abstractarray.hasOffsetArray data))
    length toIntLength toIntMax data readable writable seekable append maxsize truncate

/--
Julia source: base/iobuffer.jl:134-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function GenericIOBuffer(data::T, readable::Bool, writable::Bool, seekable::Bool, append::Bool,
                         maxsize::Integer, truncate::Bool) where T<:AbstractVector{UInt8}
    GenericIOBuffer{T}(data, readable, writable, seekable, append, maxsize, truncate)
end
```
-/
def source_GenericIOBuffer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m] {R D Index L N : Type}
    (a : Access m R D) (firstindex : D → m Index) (toIntIndex : Index → m I)
    (length : D → m L) (toIntLength : L → m I) (toIntMax : N → m I)
    (data : D) (readable writable seekable append : Bool) (maxsize : N) (truncate : Bool) : m R :=
  source_GenericIOBuffer_typed a (hasOffsetVector firstindex toIntIndex)
    length toIntLength toIntMax data readable writable seekable append maxsize truncate

abbrev genericConstructorAbstractVector := @source_GenericIOBuffer

/--
Julia source: base/iobuffer.jl:141-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function GenericIOBuffer(data::Vector{UInt8}, readable::Bool, writable::Bool, seekable::Bool, append::Bool,
                         maxsize::Integer, truncate::Bool)
    ref = data.ref
    mem = ref.mem
    offset = memoryrefoffset(ref) - 1
    # The user may pass a vector of length <= maxsize, but where the underlying memory
    # is larger than maxsize. Don't throw an error in that case.
    mz = Int(maxsize)::Int
    if !truncate && mz < length(data)
        throw(ArgumentError("maxsize must not be smaller than data length"))
    end
    buf = _new_generic_iobuffer(Memory{UInt8}, mem, readable, writable, seekable, append, mz)
    buf.offset_or_compacted = offset
    buf.ptr = offset + 1
    if truncate
        buf.size = offset
    else
        buf.size = length(data) + offset
    end
    return buf
end
```
-/
def source_GenericIOBuffer_Vector {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R Vector Memory Ref N : Type} (a : Access m R Memory)
    (reference : Vector → m Ref) (memory : Ref → m Memory) (memoryOffset : Ref → m I)
    (vectorLength : Vector → m I) (memoryLength : Memory → m I)
    (toIntMax : N → m I) (data : Vector)
    (readable writable seekable append : Bool) (maxsize : N) (truncate : Bool) : m R := do
  let reference ← reference data
  let memory ← memory reference
  let offset := JuliaLean.base.int.sub (← memoryOffset reference) one
  let mz ← toIntMax maxsize
  if !truncate then
    if JuliaLean.base.int.lt mz (← vectorLength data) then
      throw (.jl (.argumentError "maxsize must not be smaller than data length"))
  let ref ← source_new_generic_iobuffer a memoryLength
    (fun n : I => liftNative (JuliaLean.base.int.convert .i64 n))
    memory readable writable seekable append mz
  let current ← a.get ref
  a.set ref { current with offset := offset }
  let current ← a.get ref
  a.set ref { current with ptr := JuliaLean.base.int.add offset one }
  let current ← a.get ref
  if truncate then a.set ref { current with size := offset }
  else
    let size := JuliaLean.base.int.add (← vectorLength data) offset
    a.set ref { current with size := size }
  pure ref

abbrev vectorConstructor := @source_GenericIOBuffer_Vector

/--
Julia source: base/iobuffer.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_offset(io::GenericIOBuffer) = max(0, io.offset_or_compacted)
```
-/
def source_get_offset (io : BufferState) : I := imax (i 0) io.offset

/--
Julia source: base/iobuffer.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get_compacted(io::GenericIOBuffer) = max(0, -io.offset_or_compacted)
```
-/
def source_get_compacted (io : BufferState) : I := imax (i 0) (-io.offset)

/--
Julia source: base/iobuffer.jl:167-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StringMemory(n::Integer) = unsafe_wrap(Memory{UInt8}, _string_n(n))
```
-/
def source_StringMemory {m : Type → Type} [Monad m] {N S Memory : Type}
    (toCsize : N → m U) (allocateString : U → m S)
    (stringToMemory : S → m Memory) (n : N) : m Memory := do
  unsafeWrapMemory stringToMemory (← stringN toCsize allocateString n)

/--
Julia source: base/iobuffer.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StringVector(n::Integer) = wrap(Array, StringMemory(n))
```
-/
def source_StringVector {m : Type → Type} [Monad m] {N S Memory Ref Array : Type}
    (toCsize : N → m U) (allocateString : U → m S)
    (stringToMemory : S → m Memory) (memoryref : Memory → m Ref)
    (length : Memory → I) (newArray : Ref → List I → m Array) (n : N) : m Array := do
  let memory ← source_StringMemory toCsize allocateString stringToMemory n
  JuliaLean.base.array.wrapMemory memoryref length newArray memory

abbrev stringVector := @source_StringVector
def stringNModel (n : Int) : Except IOErr (List UInt8) :=
  if n < 0 || n > 2 ^ 64 - 1 then .error (.jl (.inexactError "convert"))
  else .ok (List.replicate n.toNat 0)

def unsafeWrapModel (memory : List UInt8) : Except IOErr (List UInt8) := .ok memory

def wrapArrayModel (memory : List UInt8) : Except IOErr (List UInt8) := .ok memory
def stringMemoryBytes (n : Int) : Except IOErr (List UInt8) :=
  source_StringMemory toU (fun u => .ok (List.replicate u.val.toNat 0)) unsafeWrapModel n

def stringVectorBytes (n : Int) : Except IOErr (List UInt8) :=
  source_StringVector toU (fun u => .ok (List.replicate u.val.toNat 0)) unsafeWrapModel
    (fun m => .ok m) (fun m => i m.length) (fun m _ => wrapArrayModel m) n
/--
Julia source: base/iobuffer.jl:230-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IOBuffer(
        data::AbstractVector{UInt8};
        read::Union{Bool,Nothing}=nothing,
        write::Union{Bool,Nothing}=nothing,
        append::Union{Bool,Nothing}=nothing,
        truncate::Union{Bool,Nothing}=nothing,
        maxsize::Integer=typemax(Int),
        sizehint::Union{Integer,Nothing}=nothing)
    if sizehint !== nothing
        sizehint!(data, sizehint)
    end
    flags = open_flags(read=read, write=write, append=append, truncate=truncate)
    buf = GenericIOBuffer(data, flags.read, flags.write, true, flags.append, maxsize, flags.truncate)
    return buf
end
```
-/
def source_IOBuffer_data {m : Type → Type} [Monad m] {D N Hint R : Type}
    (sizehint : D → Hint → m Unit)
    (construct : D → Bool → Bool → Bool → Bool → N → Bool → m R)
    (data : D) (read write append truncate : Option Bool) (maxsize : N)
    (hint : Option Hint) : m R := do
  match hint with
  | none => pure ()
  | some n => sizehint data n
  let flags := openFlags read write none truncate append
  construct data flags.read flags.write true flags.append maxsize flags.truncate

abbrev dataConstructor := @source_IOBuffer_data
/--
Julia source: base/iobuffer.jl:246-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IOBuffer(;
        read::Union{Bool,Nothing}=true,
        write::Union{Bool,Nothing}=true,
        append::Union{Bool,Nothing}=nothing,
        truncate::Union{Bool,Nothing}=true,
        maxsize::Integer=typemax(Int),
        sizehint::Union{Integer,Nothing}=nothing,
    )
    mz = Int(maxsize)::Int
    if mz < 0
        throw(ArgumentError("negative maxsize"))
    end
    size = if sizehint !== nothing
        # Allow negative sizehint, just like `sizehint!` does
        min(mz, max(0, Int(sizehint)::Int))
    else
        min(mz, 32)
    end
    flags = open_flags(read=read, write=write, append=append, truncate=truncate)
    # A common usecase of IOBuffer is to incrementally construct strings. By using StringMemory
    # as the default storage, we can turn the result into a string without copying.
    buf = _new_generic_iobuffer(Memory{UInt8}, StringMemory(size), flags.read, flags.write, true, flags.append, mz)
    buf.size = 0
    return buf
end
```
-/
def source_IOBuffer_empty {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {N Hint Memory L R : Type} (a : Access m R Memory)
    (toMax : N → m I) (toHint : Hint → m I) (allocate : I → m Memory)
    (length : Memory → m L) (toLength : L → m I)
    (read write append truncate : Option Bool) (maxsize : N) (hint : Option Hint) : m R := do
  let mz ← toMax maxsize
  if JuliaLean.base.int.lt mz zero then throw (.jl (.argumentError "negative maxsize"))
  let size ← match hint with
    | none => pure (JuliaLean.base.int.jmin mz (JuliaLean.base.int.lit .i64 32))
    | some n => do pure (JuliaLean.base.int.jmin mz (JuliaLean.base.int.jmax zero (← toHint n)))
  let flags := openFlags read write none truncate append
  let ref ← source_new_generic_iobuffer a length toLength (← allocate size)
    flags.read flags.write true flags.append mz
  let current ← a.get ref
  a.set ref { current with size := zero }
  pure ref

abbrev emptyConstructor := @source_IOBuffer_empty

/--
Julia source: base/iobuffer.jl:284-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PipeBuffer(data::AbstractVector{UInt8}=Memory{UInt8}(); maxsize::Int = typemax(Int)) =
    GenericIOBuffer(data, true, true, false, true, maxsize, false)
```
-/
def source_PipeBuffer_data {m : Type → Type} {D R : Type}
    (construct : D → Bool → Bool → Bool → Bool → I → Bool → m R)
    (data : D) (maxsize : I) : m R :=
  construct data true true false true maxsize false

/--
Julia source: base/iobuffer.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PipeBuffer(maxsize::Integer) = (x = PipeBuffer(StringMemory(maxsize), maxsize = maxsize); x.size = 0; x)
```
-/
def source_PipeBuffer_maxsize {m : Type → Type} [Monad m] {N Memory R : Type}
    (a : Access m R Memory) (allocate : N → m Memory)
    (assertKeywordInt : N → m I) (pipeData : Memory → I → m R) (maxsize : N) : m R := do
  let memory ← allocate maxsize
  let native ← assertKeywordInt maxsize
  let ref ← pipeData memory native
  let io ← a.get ref
  a.set ref { io with size := zero }
  pure ref

abbrev pipeMaxsize := @source_PipeBuffer_maxsize

inductive KeywordInt (N : Type) where
  | native (same : N = I)
  | other

/-- Selected Int and Csize_t conversion methods. These are callees, without laws. -/
structure IntegerConversions (N : Type) where
  toNative : N → Jl I
  toCsize : N → Jl U
  keyword : KeywordInt N

def assertKeywordInt {N : Type} (kind : KeywordInt N) (value : N) : Except IOErr I :=
  match kind with
  | .native same => .ok (same ▸ value)
  | .other => .error .typeError

def bitsConversions (t : IntTy) : IntegerConversions (JInt t) where
  toNative := JuliaLean.base.int.convert .i64
  toCsize := JuliaLean.base.int.convert .u64
  keyword := if h : t = .i64 then .native (congrArg JInt h) else .other

def boolConversions : IntegerConversions Bool where
  toNative := fun value => .ok (JuliaLean.base.int.ofBool .i64 value)
  toCsize := fun value => .ok (JuliaLean.base.int.ofBool .u64 value)
  keyword := .other

/-- Native Int-to-Int conversion in GenericIOBuffer's own body. -/
def nativeInt {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] (value : I) : m I :=
  liftNative (JuliaLean.base.int.convert .i64 value)

/-- Generic AbstractVector route, including require_one_based_indexing and
both length evaluations performed by the installed source body. -/
def pipeBuffer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    {N D Ref Index L : Type} (a : Access m Ref D)
    (firstindex : D → m Index) (toIndex : Index → m I)
    (length : D → m L) (toLength : L → m I)
    (keyword : KeywordInt N) (data : D) (maximum : N) : m Ref := do
  let maximum ← liftIO (assertKeywordInt keyword maximum)
  source_PipeBuffer_data
    (source_GenericIOBuffer a firstindex toIndex length toLength nativeInt) data maximum

/-- Vector specialization retains reference/memory/offset reads and writes. -/
def pipeBufferVector {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {N Vector Memory MemoryRef Ref : Type} (a : Access m Ref Memory)
    (reference : Vector → m MemoryRef) (memory : MemoryRef → m Memory)
    (memoryOffset : MemoryRef → m I) (vectorLength : Vector → m I)
    (memoryLength : Memory → m I) (keyword : KeywordInt N)
    (data : Vector) (maximum : N) : m Ref := do
  let maximum ← liftIO (assertKeywordInt keyword maximum)
  source_PipeBuffer_data
    (source_GenericIOBuffer_Vector a reference memory memoryOffset vectorLength memoryLength nativeInt)
    data maximum

/-- Lift the installed fixed-Except firstindex body over its deferred monadic
range operation, then run that operation. This retains effects and failures
without substituting an already-computed index or assuming a callback law. -/
def memoryFirstindex {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m] {Memory : Type}
    (length : Memory → m I) (data : Memory) : m I :=
  match JuliaLean.base.abstractarray.firstindexArray
    (fun memory => Except.ok
      (JuliaLean.base.abstractarray.eachindexDense length JuliaLean.base.range.unchecked_oneto memory))
    (fun indices => Except.ok (do
      let range ← indices
      pure (JuliaLean.base.range.first_OneTo range)))
    data with
  | .ok operation => operation
  | .error error => throwThe JuliaLean.base.abstractarray.ArrayError error

/-- Memory uses AbstractVector's has_offset_axes, not the Array shortcut.
The first length read occurs in firstindex -> eachindex before Int(maxsize);
the installed constructor performs its two later length reads unchanged. -/
def pipeMemoryData {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    {Memory Ref : Type} (a : Access m Ref Memory)
    (length : Memory → m I) (toLength : I → m I) (data : Memory) (maximum : I) : m Ref :=
  source_PipeBuffer_data
    (source_GenericIOBuffer a (memoryFirstindex length) nativeInt length toLength nativeInt)
    data maximum

/--
Julia source: base/iobuffer.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PipeBuffer(maxsize::Integer) = (x = PipeBuffer(StringMemory(maxsize), maxsize = maxsize); x.size = 0; x)
```
-/
def pipeBufferN {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    {N StringRef Memory Ref : Type} (a : Access m Ref Memory)
    (conversions : IntegerConversions N)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (length : Memory → m I) (toLength : I → m I) (maximum : N) : m Ref :=
  source_PipeBuffer_maxsize a
    (source_StringMemory (fun value => liftNative (conversions.toCsize value)) allocateString stringToMemory)
    (fun value => liftIO (assertKeywordInt conversions.keyword value))
    (pipeMemoryData a length toLength) maximum

/-- IOBuffer's allocation is the installed StringMemory body, including its
native-size Csize_t conversion and wrapping operation. -/
def iobufferEmpty {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {N Hint StringRef Memory Ref L : Type} (a : Access m Ref Memory)
    (maximum : IntegerConversions N) (hintConversion : IntegerConversions Hint)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (length : Memory → m L) (toLength : L → m I)
    (read write append truncate : Option Bool) (maxsize : N) (hint : Option Hint) : m Ref :=
  source_IOBuffer_empty a (fun value => liftNative (maximum.toNative value))
    (fun value => liftNative (hintConversion.toNative value))
    (source_StringMemory (fun size : I => liftNative (JuliaLean.base.int.convert .u64 size))
      allocateString stringToMemory)
    length toLength read write append truncate maxsize hint

/-- IOBuffer(data; ...) retains its sizehint-before-constructor call order and
binds the actual generic AbstractVector constructor. -/
def iobufferData {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    {N Hint D Ref Index L : Type} (a : Access m Ref D)
    (firstindex : D → m Index) (toIndex : Index → m I)
    (length : D → m L) (toLength : L → m I) (sizehint : D → Hint → m Unit)
    (conversions : IntegerConversions N) (data : D)
    (read write append truncate : Option Bool) (maximum : N) (hint : Option Hint) : m Ref :=
  source_IOBuffer_data sizehint
    (source_GenericIOBuffer a firstindex toIndex length toLength
      (fun value => liftNative (conversions.toNative value)))
    data read write append truncate maximum hint

/-- Separate Vector dispatch uses the installed specialized constructor. -/
def iobufferDataVector {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {N Hint Vector Memory MemoryRef Ref : Type} (a : Access m Ref Memory)
    (reference : Vector → m MemoryRef) (memory : MemoryRef → m Memory)
    (memoryOffset : MemoryRef → m I) (vectorLength : Vector → m I)
    (memoryLength : Memory → m I) (sizehint : Vector → Hint → m Unit)
    (conversions : IntegerConversions N) (data : Vector)
    (read write append truncate : Option Bool) (maximum : N) (hint : Option Hint) : m Ref :=
  source_IOBuffer_data sizehint
    (source_GenericIOBuffer_Vector a reference memory memoryOffset vectorLength memoryLength
      (fun value => liftNative (conversions.toNative value)))
    data read write append truncate maximum hint

/-- Default-keyword IOBuffer with its concrete allocation and memory operations. -/
def iobuffer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {StringRef Memory Ref L : Type} (a : Access m Ref Memory)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (length : Memory → m L) (toLength : L → m I) : m Ref :=
  iobufferEmpty a (bitsConversions .i64) (bitsConversions .i64)
    allocateString stringToMemory length toLength
    (some true) (some true) none (some true) imaxval (none : Option I)

/--
Julia source: base/iobuffer.jl:289-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _truncated_pipebuffer(data::AbstractVector{UInt8}=Memory{UInt8}(); maxsize::Int = typemax(Int))
    buf = PipeBuffer(data)
    buf.size = get_offset(buf)
    buf.maxsize = maxsize
    buf
end
```
-/
def source_truncated_pipebuffer {m : Type → Type} [Monad m] {D R Stored : Type}
    (a : Access m R Stored) (pipe : D → m R) (data : D) (maxsize : I) : m R := do
  let ref ← pipe data
  let io ← a.get ref
  a.set ref { io with size := fieldsOffset io }
  let current ← a.get ref
  a.set ref { current with maxsize }
  pure ref

abbrev truncatedPipe := @source_truncated_pipebuffer

/--
Julia source: base/iobuffer.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_data(b::GenericIOBuffer, len::Int) = similar(b.data, len)
```
-/
def source_similar_data_generic {m : Type → Type} [Monad m] {R D NewData : Type}
    (a : Access m R D) (similar : D → I → m NewData) (ref : R) (length : I) : m NewData := do
  similar (← a.get ref).data length

abbrev similarDataGeneric := @source_similar_data_generic

/--
Julia source: base/iobuffer.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_data(b::IOBuffer, len::Int) = StringMemory(len)
```
-/
def source_similar_data_IOBuffer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R Memory StringRef : Type} (_a : Access m R Memory)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (_ref : R) (length : I) : m Memory :=
  source_StringMemory (fun n : I => liftNative (JuliaLean.base.int.convert .u64 n))
    allocateString stringToMemory length

abbrev similarDataIOBuffer := @source_similar_data_IOBuffer

/--
Julia source: base/iobuffer.jl:302-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy(b::GenericIOBuffer{T}) where T
    if b.reinit
        # If buffer is used up, allocate a new size-zero buffer
        # Reinit implies writable, and that ptr, size, offset and mark are already the default values
        return typeof(b)(_similar_data(b, 0), b.readable, b.writable, b.seekable, b.append, b.maxsize, false)
    elseif b.writable
        # Else, we just copy the reachable bytes. If buffer is seekable, all bytes
        # after offset are reachable, since they can be seeked to
        used_span = get_used_span(b)
        compacted = first(used_span) - get_offset(b) - 1
        len = length(used_span)
        data = copyto!(_similar_data(b, len), view(b.data, used_span))
        ret = typeof(b)(data, b.readable, b.writable, b.seekable, b.append, b.maxsize, false)
        ret.size = len
        # Copying data over implicitly compacts, and may add compaction
        ret.offset_or_compacted = -get_compacted(b) - compacted
        ret.ptr = b.ptr - first(used_span) + 1
        ret.mark = b.mark
        return ret
    else
        # When the buffer is just readable, they can share the same data, so we just make
        # a shallow copy of the IOBuffer struct.
        # Use internal constructor because we want to allow b.maxsize to be larger than data,
        # in case that is the case for `b`.
        ret = _new_generic_iobuffer(T, b.data, b.readable, b.writable, b.seekable, b.append, b.maxsize)
        ret.offset_or_compacted = b.offset_or_compacted
        ret.ptr = b.ptr
        ret.mark = b.mark
        return ret
    end
end
```
-/
def source_copy (similar : BufferState → I → Except IOErr (List UInt8))
    (construct : List UInt8 → Bool → Bool → Bool → Bool → I → Bool → Except IOErr BufferState)
    (b : BufferState) : Except IOErr BufferState := do
  if b.reinit then
    construct (← similar b (i 0)) b.readable b.writable b.seekable b.append b.maxsize false
  else if b.writable then
    let usedSpan ← getUsedSpan b
    let compacted := usedSpan.1 - getOffset b - i 1
    let len := rangeLength usedSpan.1 usedSpan.2
    let data0 ← similar b len
    let data ← copyto data0 (i 1) b.data usedSpan.1 len
    let ret ← construct data b.readable b.writable b.seekable b.append b.maxsize false
    let ret := { ret with size := len }
    let ret := { ret with offset := -getCompacted b - compacted }
    let ret := { ret with ptr := b.ptr - usedSpan.1 + i 1 }
    pure { ret with mark := b.mark }
  else
    let ret := newBuf b.data b.isMemory b.readable b.writable b.seekable b.append b.maxsize
    let ret := { ret with offset := b.offset, ptr := b.ptr }
    pure { ret with mark := b.mark }

/--
Julia source: base/iobuffer.jl:334-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, b::GenericIOBuffer) = print(io, "IOBuffer(data=UInt8[...], ",
                                      "readable=", b.readable, ", ",
                                      "writable=", b.writable, ", ",
                                      "seekable=", b.seekable, ", ",
                                      "append=",   b.append, ", ",
                                      "size=",     b.size - get_offset(b), ", ",
                                      "maxsize=",  b.maxsize == typemax(Int) ? "Inf" : b.maxsize, ", ",
                                      "ptr=",      b.ptr - get_offset(b), ", ",
                                      "mark=",     b.mark, ")")
```
-/
def source_show {m : Type → Type} [Monad m] {E R D Out : Type} [MonadExceptOf E m]
    (a : Access m R D) (lock unlock : Out → m Unit)
    (printOne : Out → ShowArgument → m Unit) (out : Out) (ref : R) : m Unit := do
  let io ← a.get ref
  printArgs (E := E) lock unlock printOne out
    [.text "IOBuffer(data=UInt8[...], ", .text "readable=", .boolean io.readable,
     .text ", ", .text "writable=", .boolean io.writable, .text ", ",
     .text "seekable=", .boolean io.seekable, .text ", ",
     .text "append=", .boolean io.append, .text ", ",
     .text "size=", .integer (JuliaLean.base.int.sub io.size (fieldsOffset io)), .text ", ",
     .text "maxsize=", if JuliaLean.base.int.eq_int io.maxsize (JInt.typemax .i64) then .text "Inf"
       else .integer io.maxsize,
     .text ", ", .text "ptr=", .integer (JuliaLean.base.int.sub io.ptr (fieldsOffset io)),
     .text ", ", .text "mark=", .integer io.mark, .text ")"]

/--
Julia source: base/iobuffer.jl:344-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function _throw_not_readable()
    # See https://github.com/JuliaLang/julia/issues/29688.
    throw(ArgumentError("read failed, IOBuffer is not readable"))
end
```
-/
def source_throw_not_readable {α : Type} : Except IOErr α :=
  .error (.jl (.argumentError "read failed, IOBuffer is not readable"))

/--
Julia source: base/iobuffer.jl:349-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_read(from::GenericIOBuffer, p::Ptr{UInt8}, nb::UInt)
    from.readable || _throw_not_readable()
    avail = bytesavailable(from) % UInt
    adv = min(avail, nb)
    unsafe_read!(p, from.data, from.ptr, adv)
    from.ptr += adv
    if nb > avail
        throw(EOFError())
    end
    nothing
end
```
-/
def source_unsafe_read {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D P : Type}
    (a : Access m R D) (readBang : P → D → I → U → m Unit)
    (ref : R) (dest : P) (count : U) : m Unit := do
  let io ← a.get ref
  if !io.readable then liftIO JuliaLean.base.iobuffer.source_throw_not_readable
  let avail := JuliaLean.base.int.remT .u64 (fieldsBytesavailable io)
  let advance := JuliaLean.base.int.jmin avail count
  readBang dest io.data io.ptr advance
  let current ← a.get ref
  let nextPtr ← liftNative (JuliaLean.base.int.convert .i64
    (JuliaLean.base.int.binop JuliaLean.base.int.add current.ptr advance))
  a.set ref { current with ptr := nextPtr }
  if JuliaLean.base.int.lt avail count then throw .eofError

def unsafeReadInt {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D : Type}
    (a : Access m R D)
    (readBang : JuliaLean.base.pointer.Ptr Byte → D → I → U → m Unit)
    (ref : R) (dest : JuliaLean.base.pointer.Ptr Byte) (requested : I) : m Unit := do
  let pointer := JuliaLean.base.pointer.convertPtrSame dest
  let count ← liftNative (JuliaLean.base.int.convert .u64 requested)
  source_unsafe_read a readBang ref pointer count

/--
Julia source: base/iobuffer.jl:361-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_read!(dest::Ptr{UInt8}, src::AbstractVector{UInt8}, so::Integer, nbytes::UInt)
    for i in 1:nbytes
        unsafe_store!(dest, @inbounds(src[so+i-1]), i)
    end
end
```
-/
def source_unsafe_read_vector {m : Type → Type} [Monad m] {D P Start Index : Type}
    (sourceIndex : Start → U → m Index) (getindex : D → Index → m Byte)
    (store : P → Byte → U → m Unit) (dest : P) (data : D) (start : Start) (count : U) : m Unit := do
  for k in List.range count.val.toNat do
    let index := JuliaLean.base.int.lit .u64 (k + 1)
    let byte ← getindex data (← sourceIndex start index)
    store dest byte index

/--
Julia source: base/iobuffer.jl:375-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_read!(dest::Ptr{UInt8}, src::DenseBytes, so::Integer, nbytes::UInt)
    GC.@preserve src unsafe_copyto!(dest, pointer(src, so), nbytes)
    nothing
end
```
-/
def source_unsafe_read_dense {m : Type → Type} [Monad m] {D P Start : Type}
    (pointer : D → Start → m P) (copy : P → P → U → m P)
    (dest : P) (data : D) (start : Start) (count : U) : m Unit := do
  let _ ← copy dest (← pointer data start) count
  pure ()

/--
Julia source: base/iobuffer.jl:394-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function load_from_array(T::MultiByteBitNumberType, data::AbstractArray{UInt8}, from::Int)
    x = if T <: AbstractFloat
        uinttype(T)(0)
    else
        unsigned(T)(0)
    end
    for i in 0:sizeof(x)-1
        x |= typeof(x)(data[from + i]) << (8 * i)
    end
    reinterpret(T, ltoh(x))
end
```
-/
def source_load_from_array {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {D : Type}
    (getindex : D → I → m Byte)
    (ltoh : (t : IntTy) → JInt t → m (JInt t))
    (full : (kind : Multibyte) → JInt (wordType kind) → m (valueType kind))
    (kind : Multibyte) (data : D) (first : I) : m (valueType kind) := do
  let mut word := initialWord kind
  let size := JuliaLean.base.int.sizeof word
  for k in List.range size.val.toNat do
    let index := JuliaLean.base.int.lit .i64 k
    let byte ← getindex data (JuliaLean.base.int.add first index)
    let converted ← liftNative (JuliaLean.base.int.convert (wordType kind) byte)
    word := JuliaLean.base.int.bor word (JuliaLean.base.int.shl_Int converted
      (JuliaLean.base.int.mul (JuliaLean.base.int.lit .i64 8) index))
  reinterpretWord full kind (← ltoh (wordType kind) word)

abbrev loadFromArray := @source_load_from_array

/--
Julia source: base/iobuffer.jl:406-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek(from::GenericIOBuffer, T::MultiByteBitNumberType)
    from.readable || _throw_not_readable()
    avail = bytesavailable(from)
    nb = sizeof(T)
    if nb > avail
        throw(EOFError())
    end
    return load_from_array(T, from.data, from.ptr)
end
```
-/
def source_peek_multibyte {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D : Type}
    (a : Access m R D) (getindex : D → I → m Byte)
    (ltoh : (t : IntTy) → JInt t → m (JInt t))
    (full : (kind : Multibyte) → JInt (wordType kind) → m (valueType kind))
    (ref : R) (kind : Multibyte) : m (valueType kind) := do
  let io ← a.get ref
  if !io.readable then liftIO source_throw_not_readable
  let count := JuliaLean.base.int.sizeof (initialWord kind)
  if JuliaLean.base.int.lt (fieldsBytesavailable io) count then throw .eofError
  source_load_from_array getindex ltoh full kind io.data io.ptr

abbrev peekArray := @source_peek_multibyte

/--
Julia source: base/iobuffer.jl:418-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek(from::GenericIOBuffer{<:MutableDenseArrayType}, T::MultiByteBitNumberType)
    from.readable || _throw_not_readable()
    avail = bytesavailable(from)
    nb = sizeof(T)
    if nb > avail
        throw(EOFError())
    end
    GC.@preserve from begin
        ptr::Ptr{T} = pointer(from.data, from.ptr)
        x = unsafe_load(ptr)
    end
    return x
end
```
-/
def source_peek_multibyte_dense {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m] {R D : Type}
    (a : Access m R D) (h : HeapAccess m)
    (codec : (kind : Multibyte) → JuliaLean.base.pointer.ByteCodec (valueType kind))
    (pointer : D → I → m (JuliaLean.base.pointer.Ptr Byte))
    (preserve : (kind : Multibyte) → R → (Unit → m (valueType kind)) → m (valueType kind))
    (ref : R) (kind : Multibyte) : m (valueType kind) := do
  let io ← a.get ref
  if !io.readable then liftIO source_throw_not_readable
  let count := JuliaLean.base.int.sizeof (initialWord kind)
  if JuliaLean.base.int.lt (fieldsBytesavailable io) count then throwThe IOErr .eofError
  preserve kind ref (fun _ => do
    let current ← a.get ref
    let ptr ← pointer current.data current.ptr
    let typed : JuliaLean.base.pointer.Ptr (valueType kind) := JuliaLean.base.pointer.convertPtrType ptr
    let heap ← h.get
    match JuliaLean.base.pointer.unsafeLoad (codec kind)
        (fun n : I => (JuliaLean.base.int.convert .i64 n).mapError
          JuliaLean.base.pointer.PointerError.julia) typed heap one with
    | .ok value => pure value
    | .error error => throwThe JuliaLean.base.pointer.PointerError error)

abbrev peekDense := @source_peek_multibyte_dense

/--
Julia source: base/iobuffer.jl:432-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(from::GenericIOBuffer, T::MultiByteBitNumberType)
    x = peek(from, T)
    from.ptr += sizeof(T)
    return x
end
```
-/
def source_read_multibyte {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D : Type}
    (a : Access m R D) (getindex : D → I → m Byte)
    (ltoh : (t : IntTy) → JInt t → m (JInt t))
    (full : (kind : Multibyte) → JInt (wordType kind) → m (valueType kind))
    (ref : R) (kind : Multibyte) : m (valueType kind) := do
  let value ← source_peek_multibyte a getindex ltoh full ref kind
  let current ← a.get ref
  a.set ref { current with
    ptr := JuliaLean.base.int.add current.ptr (JuliaLean.base.int.sizeof (initialWord kind)) }
  pure value

abbrev readMultibyteArray := @source_read_multibyte

def readMultibyteDense {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m] {R D : Type}
    (a : Access m R D) (h : HeapAccess m)
    (codec : (kind : Multibyte) → JuliaLean.base.pointer.ByteCodec (valueType kind))
    (pointer : D → I → m (JuliaLean.base.pointer.Ptr Byte))
    (preserve : (kind : Multibyte) → R → (Unit → m (valueType kind)) → m (valueType kind))
    (ref : R) (kind : Multibyte) : m (valueType kind) := do
  let value ← source_peek_multibyte_dense a h codec pointer preserve ref kind
  let current ← a.get ref
  a.set ref { current with
    ptr := JuliaLean.base.int.add current.ptr (JuliaLean.base.int.sizeof (initialWord kind)) }
  pure value

/--
Julia source: base/iobuffer.jl:438-448 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function read(from::GenericIOBuffer, ::Type{UInt8})
    from.readable || _throw_not_readable()
    ptr = from.ptr
    size = from.size
    if ptr > size
        throw(EOFError())
    end
    @inbounds byte = from.data[ptr]::UInt8
    from.ptr = ptr + 1
    return byte
end
```
-/
def source_read_uint8 {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D : Type}
    (a : Access m R D) (getindex : D → I → m Byte) (ref : R) : m Byte := do
  let io ← a.get ref
  if !io.readable then liftIO JuliaLean.base.iobuffer.source_throw_not_readable
  let ptr := io.ptr
  let size := io.size
  if JuliaLean.base.int.lt size ptr then throw .eofError
  let byte ← getindex io.data ptr
  let current ← a.get ref
  a.set ref { current with ptr := JuliaLean.base.int.add ptr one }
  pure byte

/--
Julia source: base/iobuffer.jl:450-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek(from::GenericIOBuffer, ::Type{UInt8})
    from.readable || _throw_not_readable()
    if from.ptr > from.size
        throw(EOFError())
    end
    return from.data[from.ptr]::UInt8
end
```
-/
def source_peek_uint8 : M UInt8 := do
  let sourceBuf ← get
  if !sourceBuf.readable then throwNotReadable
  if sourceBuf.ptr.val > sourceBuf.size.val then throw .eofError
  lift (getChecked sourceBuf.data sourceBuf.ptr)

/--
Julia source: base/iobuffer.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(from::GenericIOBuffer, ::Type{Ptr{T}}) where {T} = convert(Ptr{T}, read(from, UInt))
```
-/
def source_read_pointer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D T : Type}
    (a : Access m R D) (getindex : D → I → m Byte)
    (ltoh : (t : IntTy) → JInt t → m (JInt t))
    (full : (kind : Multibyte) → JInt (wordType kind) → m (valueType kind))
    (ref : R) : m (JuliaLean.base.pointer.Ptr T) := do
  let word ← source_read_multibyte a getindex ltoh full ref .u64
  pure (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor
    (.unsigned word))

abbrev readPointerArray := @source_read_pointer

def readPointerDense {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m] {R D T : Type}
    (a : Access m R D) (h : HeapAccess m)
    (codec : (kind : Multibyte) → JuliaLean.base.pointer.ByteCodec (valueType kind))
    (pointer : D → I → m (JuliaLean.base.pointer.Ptr Byte))
    (preserve : (kind : Multibyte) → R → (Unit → m (valueType kind)) → m (valueType kind))
    (ref : R) : m (JuliaLean.base.pointer.Ptr T) := do
  let word ← readMultibyteDense a h codec pointer preserve ref .u64
  pure (JuliaLean.base.pointer.convertIntegerToPtrMethod pointerConstructor (.unsigned word))

/--
Julia source: base/iobuffer.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isreadable(io::GenericIOBuffer) = io.readable
```
-/
def source_isreadable (io : BufferState) : Bool := io.readable

/--
Julia source: base/iobuffer.jl:461-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iswritable(io::GenericIOBuffer) = io.writable
```
-/
def source_iswritable (io : BufferState) : Bool := io.writable

/--
Julia source: base/iobuffer.jl:464-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filesize(io::GenericIOBuffer) = (io.seekable ? io.size - get_offset(io) : bytesavailable(io))
```
-/
def source_filesize (io : BufferState) : I :=
  if io.seekable then io.size - getOffset io else bytesavailable io

/--
Julia source: base/iobuffer.jl:467-467 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bytesavailable(io::GenericIOBuffer) = io.size - io.ptr + 1
```
-/
def source_bytesavailable (io : BufferState) : I := io.size - io.ptr + i 1

/--
Julia source: base/iobuffer.jl:470-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function position(io::GenericIOBuffer)
    # Position is zero-indexed, but ptr is one-indexed, hence the -1
    io.ptr - io.offset_or_compacted - 1
end
```
-/
def source_position (io : BufferState) : I := io.ptr - io.offset - i 1

/--
Julia source: base/iobuffer.jl:475-477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function skip(io::GenericIOBuffer, n::Integer)
    skip(io, clamp(n, Int))
end
```
-/
def source_skip_integer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R N : Type}
    (skipInt : R → I → m R) (gt lt : N → I → Bool) (convert : N → Jl I) (ref : R) (n : N) : m R := do
  skipInt ref (← liftIO (clampInteger gt lt convert n))

/--
Julia source: base/iobuffer.jl:479-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function skip(io::GenericIOBuffer, n::Int)
    # In both cases, the result will never go to before the first position,
    # nor beyond the last position, and will not throw an error unless the stream
    # is not seekable and try to skip a negative number of bytes.
    if signbit(n)
        # Skipping a negative number of bytes is equivalent to seeking backwards.
        seekto = clamp(widen(position(io)) + widen(n), Int)
        seek(io, seekto) # Does error checking
    else
        # Don't use seek in order to allow a non-seekable IO to still skip bytes.
        # Handle overflow.
        n_max = io.size + 1 - io.ptr
        io.ptr += min(n, n_max)
        io
    end
end
```
-/
def source_skip {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D : Type}
    (a : Access m R D) (seekInt : R → I → m R) (ref : R) (n : I) : m R := do
  if JuliaLean.base.int.signbit n then
    let io ← a.get ref
    let target := JuliaLean.base.int.add (JuliaLean.base.int.widenTo .i128 (fieldsPosition io))
      (JuliaLean.base.int.widenTo .i128 n)
    seekInt ref (← liftIO (clampBits target))
  else
    let io ← a.get ref
    let nmax := JuliaLean.base.int.sub (JuliaLean.base.int.add io.size one) io.ptr
    a.set ref { io with ptr := JuliaLean.base.int.add io.ptr (JuliaLean.base.int.jmin n nmax) }
    pure ref

/--
Julia source: base/iobuffer.jl:496-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function seek(io::GenericIOBuffer, n::Integer)
    seek(io, clamp(n, Int))
end
```
-/
def source_seek_integer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R N : Type}
    (seekInt : R → I → m R) (gt lt : N → I → Bool) (convert : N → Jl I) (ref : R) (n : N) : m R := do
  seekInt ref (← liftIO (clampInteger gt lt convert n))

/--
Julia source: base/iobuffer.jl:500-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function translate_seek_position(io::GenericIOBuffer, n::Int)
    # If there is an offset (the field F is positive), then there are F unused bytes at the beginning
    # of the data, and we need to seek to n + F + 1. (Also compensate for `seek` being zero-
    # indexed)

    # If bytes has been compacted (field F is negative), then F bytes has been deleted from
    # the buffer, and a virtual position n means a position n + F in the data.
    # Remember that F is negative, so n + F is subtracting from n. So we also end up with
    # n + F + 1.
    clamp(widen(n) + widen(io.offset_or_compacted) + widen(1), Int)
end
```
-/
def source_translate_seek_position {D : Type} (io : Fields D) (n : I) : Except IOErr I :=
  let target := JuliaLean.base.int.add
    (JuliaLean.base.int.add (JuliaLean.base.int.widenTo .i128 n)
      (JuliaLean.base.int.widenTo .i128 io.offset))
    (JuliaLean.base.int.widenTo .i128 one)
  clampBits target

abbrev translate := @source_translate_seek_position

/--
Julia source: base/iobuffer.jl:512-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function seek(io::GenericIOBuffer, n::Int)
    if !io.seekable
        ismarked(io) || throw(ArgumentError("seek failed, IOBuffer is not seekable and is not marked"))
        n == io.mark || throw(ArgumentError("seek failed, IOBuffer is not seekable and n != mark"))
    end

    # TODO: REPL.jl relies on the fact that this does not throw (by seeking past the beginning or end
    #       of a GenericIOBuffer), so that would need to be fixed in order to throw an error here
    max_ptr = io.size + 1
    min_ptr = get_offset(io) + 1
    io.ptr = clamp(translate_seek_position(io, n), min_ptr, max_ptr)
    return io
end
```
-/
def source_seek {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D : Type}
    (a : Access m R D) (ref : R) (n : I) : m R := do
  let io ← a.get ref
  if !io.seekable then
    if !fieldsIsmarked io then
      throw (.jl (.argumentError "seek failed, IOBuffer is not seekable and is not marked"))
    if !(JuliaLean.base.int.eq_int n io.mark) then
      throw (.jl (.argumentError "seek failed, IOBuffer is not seekable and n != mark"))
  let maxPtr := JuliaLean.base.int.add io.size one
  let minPtr := JuliaLean.base.int.add (fieldsOffset io) one
  let target ← liftIO (source_translate_seek_position io n)
  let ptr ← liftNative (JuliaLean.base.intfuncs.clamp
    (fun x hi => JuliaLean.base.int.lt hi x) JuliaLean.base.int.lt
    (JuliaLean.base.int.convert .i64) (JuliaLean.base.int.convert .i64)
    (JuliaLean.base.int.convert .i64) target minPtr maxPtr)
  a.set ref { io with ptr }
  pure ref

/--
Julia source: base/iobuffer.jl:526-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function seekend(io::GenericIOBuffer)
    io.ptr = io.size+1
    return io
end
```
-/
def source_seekend {m : Type → Type} [Monad m] {R D : Type} (a : Access m R D) (ref : R) : m R := do
  let io ← a.get ref
  a.set ref { io with ptr := JuliaLean.base.int.add io.size one }
  pure ref

/--
Julia source: base/iobuffer.jl:662-673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_used_span(io::IOBuffer)
    # A seekable buffer can recover data before ptr
    return if io.seekable
        get_offset(io) + 1 : io.size
    # If non-seekable, the mark can be used to recover data before ptr,
    # so data at the mark and after must also be saved
    elseif io.mark > -1
        min(io.ptr, translate_seek_position(io, io.mark)) : io.size
    else
        io.ptr : io.size
    end
end
```
-/
def source_get_used_span {D : Type} (io : Fields D) : Except IOErr (I × I) := do
  if io.seekable then pure (JuliaLean.base.int.add (fieldsOffset io) one, io.size)
  else if JuliaLean.base.int.lt (JuliaLean.base.int.lit .i64 (-1)) io.mark then
    pure (JuliaLean.base.int.jmin io.ptr (← source_translate_seek_position io io.mark), io.size)
  else pure (io.ptr, io.size)

def dispatchUsedSpan {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D : Type}
    (a : Access m R D) (ref : R) : m (I × I) := do
  if ← a.isIOBuffer ref then liftIO (source_get_used_span (← a.get ref))
  else throw (.jl (.methodError "get_used_span"))

/--
Julia source: base/iobuffer.jl:677-689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compact!(io::GenericIOBuffer)::Int
    offset = get_offset(io)
    used_span = get_used_span(io)
    deleted = first(used_span) - 1
    compacted = deleted - offset
    iszero(deleted) && return 0
    data = io.data
    copyto!(data, 1, data, deleted + 1, length(used_span))
    io.offset_or_compacted = -get_compacted(io) - compacted
    io.ptr -= deleted
    io.size -= deleted
    return deleted
end
```
-/
def source_compact {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData : Type}
    (a : Access m R D) (s : Storage m R D NewData) (ref : R) : m I := do
  let io ← a.get ref
  let offset := fieldsOffset io
  let (first, last) ← dispatchUsedSpan a ref
  let deleted := JuliaLean.base.int.sub first one
  let compacted := JuliaLean.base.int.sub deleted offset
  if ← iszeroInt deleted then return zero
  s.copyWithin io.data one io.data (JuliaLean.base.int.add deleted one) (← s.spanLength first last)
  let current ← a.get ref
  a.set ref { current with
    offset := JuliaLean.base.int.sub (JuliaLean.base.int.neg_int (fieldsCompacted current)) compacted
    ptr := JuliaLean.base.int.sub current.ptr deleted
    size := JuliaLean.base.int.sub current.size deleted }
  pure deleted

/--
Julia source: base/iobuffer.jl:536-556 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _resize!(io::GenericIOBuffer, new_size::Int, exact::Bool)
    old_data = io.data
    if applicable(resize!, old_data, new_size)
        resize!(old_data, new_size)
    else
        new_size = exact ? new_size : min(io.maxsize, overallocation(new_size))
        used_span = get_used_span(io)
        deleted = first(used_span) - 1
        compacted = deleted - get_offset(io)
        new_data = _similar_data(io, new_size)
        io.data = new_data
        iszero(new_size) && return io
        len_used = length(used_span)
        iszero(len_used) || copyto!(new_data, 1, old_data, first(used_span), len_used)
        # Copying will implicitly compact, and so compaction must be updated
        io.offset_or_compacted = -get_compacted(io) - compacted
        io.ptr -= deleted
        io.size = len_used
    end
    return io
end
```
-/
def source_resize {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData : Type}
    (a : Access m R D) (s : Storage m R D NewData) (ref : R) (requested : I) (exact : Bool) : m R := do
  let io ← a.get ref
  let oldData := io.data
  if ← s.applicableResize oldData requested then s.resize oldData requested
  else
    let size ← if exact then pure requested
      else pure (JuliaLean.base.int.jmin io.maxsize (← sourceOverallocation requested))
    let (first, last) ← dispatchUsedSpan a ref
    let deleted := JuliaLean.base.int.sub first one
    let compacted := JuliaLean.base.int.sub deleted (fieldsOffset io)
    let newData ← s.similar ref size
    let converted ← s.convertData newData
    let current ← a.get ref
    a.set ref { current with data := converted }
    if ← iszeroInt size then return ref
    let used ← s.spanLength first last
    if !(← iszeroInt used) then s.copyIntoNew newData one oldData first used
    let current ← a.get ref
    a.set ref { current with
      offset := JuliaLean.base.int.sub (JuliaLean.base.int.neg_int (fieldsCompacted current)) compacted
      ptr := JuliaLean.base.int.sub current.ptr deleted
      size := used }
  pure ref

/--
Julia source: base/iobuffer.jl:618-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function ensureroom_reallocate(io::GenericIOBuffer, nshort::UInt)
    io.writable || throw(ArgumentError("ensureroom failed, IOBuffer is not writeable"))
    io.data = _similar_data(io, min(io.maxsize, nshort % Int))
    io.reinit = false
    io.offset_or_compacted = -get_compacted(io)
    return io
end
```
-/
def source_ensureroom_reallocate {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData : Type}
    (a : Access m R D) (s : Storage m R D NewData) (ref : R) (count : U) : m R := do
  let io ← a.get ref
  if !io.writable then throw (.jl (.argumentError "ensureroom failed, IOBuffer is not writeable"))
  let data ← s.similar ref (JuliaLean.base.int.jmin io.maxsize (JuliaLean.base.int.remT .i64 count))
  let converted ← s.convertData data
  let current ← a.get ref
  a.set ref { current with data := converted }
  let current ← a.get ref
  a.set ref { current with reinit := false }
  let current ← a.get ref
  a.set ref { current with offset := JuliaLean.base.int.neg_int (fieldsCompacted current) }
  pure ref

def resizeArgument {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R D NewData Other : Type} (a : Access m R D) (s : Storage m R D NewData)
    (ref : R) (requested : I ⊕ Other) (exact : Bool) : m R :=
  match requested with
  | .inl value => source_resize a s ref value exact
  | .inr _ => throw (.jl (.methodError "_resize!"))

/--
Julia source: base/iobuffer.jl:627-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function ensureroom_slowpath(io::GenericIOBuffer, nshort::UInt, available_bytes::Int)
    reclaimable_bytes = first(get_used_span(io)) - 1
    # Avoid resizing and instead compact the buffer, only if we gain enough bytes from
    # doing so (at least 32 bytes and 1/8th of the data length). Also, if we would have
    # to resize anyway, there would be no point in compacting, so also check that.
    if (
            reclaimable_bytes ≥ 32 &&
            reclaimable_bytes ≥ length(io.data) >>> 3 &&
            (reclaimable_bytes + available_bytes) % UInt ≥ nshort
        )
        compact!(io)
        return io
    end

    desired_size = length(io.data) + Int(nshort) - available_bytes
    if desired_size > io.maxsize
        # If we can't fit all the requested data in the new buffer, we need to
        # fit as much as possible, so we must compact
        if !iszero(reclaimable_bytes)
            compact!(io)
        end
        # Max out the buffer size if we want more than the buffer size
        if length(io.data) < io.maxsize
            _resize!(io, io.maxsize, true)
        end
    else
        # Else, we request only the requested size, but set `exact` to `false`,
        # in order to overallocate to avoid growing the buffer by too little
        _resize!(io, desired_size, false)
    end

    return io
end
```
-/
def source_ensureroom_slowpath {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData : Type}
    (a : Access m R D) (s : Storage m R D NewData) (ref : R) (count : U) (available : I) : m R := do
  let (first, _) ← dispatchUsedSpan a ref
  let reclaimable := JuliaLean.base.int.sub first one
  let shouldCompact ← if JuliaLean.base.int.le (JuliaLean.base.int.lit .i64 32) reclaimable then do
      let current ← a.get ref
      let length ← s.length current.data
      if ← s.reclaimEnough reclaimable (← s.shiftLength length) then
        pure (JuliaLean.base.int.le count
          (JuliaLean.base.int.remT .u64 (JuliaLean.base.int.add reclaimable available)))
      else pure false
    else pure false
  if shouldCompact then
    let _ ← source_compact a s ref
    return ref
  let current ← a.get ref
  let length ← s.length current.data
  let native ← liftNative (JuliaLean.base.int.convert .i64 count)
  let desired ← s.subtractAvailable (← s.addLength length native) available
  let current ← a.get ref
  if ← s.desiredGreater desired current.maxsize then
    if !(← iszeroInt reclaimable) then
      let _ ← source_compact a s ref
      pure ()
    let current ← a.get ref
    let length ← s.length current.data
    let current ← a.get ref
    if ← s.lengthLess length current.maxsize then
      let current ← a.get ref
      let _ ← source_resize a s ref current.maxsize true
      pure ()
  else
    let _ ← resizeArgument a s ref desired false
    pure ()
  pure ref

def slowpathArgument {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R D NewData Other : Type} (a : Access m R D) (s : Storage m R D NewData)
    (ref : R) (count : U) (available : I ⊕ Other) : m R :=
  match available with
  | .inl value => source_ensureroom_slowpath a s ref count value
  | .inr _ => throw (.jl (.methodError "ensureroom_slowpath"))

/--
Julia source: base/iobuffer.jl:599-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function ensureroom(io::GenericIOBuffer, nshort::UInt)
    # If the IO is not writable, we call the slow path only to error.
    # If reinit, the data has been handed out to the user, and the IOBuffer
    # no longer controls it, so we need to allocate a new one.
    if !io.writable || io.reinit
        return ensureroom_reallocate(io, nshort)
    end
    # The fast path here usually checks there is already room, then does nothing.
    # When append is true, new data is added after io.size, not io.ptr
    start_offset = io.append ? io.size : io.ptr - 1
    existing_space = min(lastindex(io.data) - start_offset, io.maxsize - (start_offset - get_offset(io)))
    if existing_space < nshort % Int
        # Outline this function to make it more likely that ensureroom inlines itself
        return ensureroom_slowpath(io, nshort, existing_space)
    end
    return io
end
```
-/
def source_ensureroom {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData : Type}
    (a : Access m R D) (s : Storage m R D NewData) (ref : R) (count : U) : m R := do
  let io ← a.get ref
  if !io.writable || io.reinit then return (← source_ensureroom_reallocate a s ref count)
  let start := if io.append then io.size else JuliaLean.base.int.sub io.ptr one
  let difference ← s.subtractIndex (← s.lastIndex io.data) start
  let current ← a.get ref
  let capacity := JuliaLean.base.int.sub current.maxsize
    (JuliaLean.base.int.sub start (fieldsOffset current))
  let existing ← s.minimumSpace difference capacity
  if ← s.spaceLess existing (JuliaLean.base.int.remT .i64 count) then
    return (← slowpathArgument a s ref count existing)
  pure ref

/--
Julia source: base/iobuffer.jl:597-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline ensureroom(io::GenericIOBuffer, nshort::Int) = ensureroom(io, UInt(nshort))
```
-/
def source_ensureroom_int {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData : Type}
    (a : Access m R D) (s : Storage m R D NewData) (ref : R) (count : I) : m R := do
  source_ensureroom a s ref (← liftNative (JuliaLean.base.int.convert .u64 count))

/--
Julia source: base/iobuffer.jl:558-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function truncate(io::GenericIOBuffer, n::Integer)
    io.writable || throw(ArgumentError("truncate failed, IOBuffer is not writeable"))
    # Non-seekable buffers can only be constructed with `PipeBuffer`, which is explicitly
    # documented to not be truncatable.
    io.seekable || throw(ArgumentError("truncate failed, IOBuffer is not seekable"))
    n < 0 && throw(ArgumentError("truncate failed, n bytes must be ≥ 0, got $n"))
    n > io.maxsize && throw(ArgumentError("truncate failed, $(n) bytes is exceeds IOBuffer maxsize $(io.maxsize)"))
    n = Int(n)::Int
    offset = get_offset(io)
    current_size = io.size - offset
    if io.reinit
        # If reinit, we don't need to truncate anything but just reinitializes
        # the buffer with zeros. Mark, ptr and offset has already been reset.
        io.data = fill!(_similar_data(io, n), 0x00)
        io.reinit = false
        io.size = n
    elseif n < current_size
        # Else, if we need to shrink the iobuffer, we simply change the pointers without
        # actually shrinking the underlying storage, or copying data.

        # Clear the mark if it points to data that has now been deleted.
        if translate_seek_position(io, io.mark) > n+offset
            io.mark = -1
        end
        io.size = n + offset
        io.ptr = min(io.ptr, n + offset + 1)
    elseif n > current_size
        if n + offset > io.maxsize
            compact!(io)
        end
        _resize!(io, n + get_offset(io), false)
        fill!(view(io.data, io.size + 1:min(length(io.data), n + get_offset(io))), 0x00)
        io.size = min(length(io.data), n + get_offset(io))
    end
    return io
end
```
-/
def source_truncate {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData N : Type}
    (a : Access m R D) (s : Storage m R D NewData)
    (negative : N → m Bool) (exceeds : N → I → m Bool) (toInt : N → m I)
    (showN : N → String) (ref : R) (requested : N) : m R := do
  let io ← a.get ref
  if !io.writable then throw (.jl (.argumentError "truncate failed, IOBuffer is not writeable"))
  let io ← a.get ref
  if !io.seekable then throw (.jl (.argumentError "truncate failed, IOBuffer is not seekable"))
  if ← negative requested then
    throw (.jl (.argumentError ("truncate failed, n bytes must be ≥ 0, got " ++ showN requested)))
  let io ← a.get ref
  if ← exceeds requested io.maxsize then
    throw (.jl (.argumentError ("truncate failed, " ++ showN requested ++
      " bytes is exceeds IOBuffer maxsize " ++ toString io.maxsize.val)))
  let n ← toInt requested
  let io ← a.get ref
  let offset := fieldsOffset io
  let currentSize := JuliaLean.base.int.sub io.size offset
  if io.reinit then
    let newData ← s.similar ref n
    s.fillNew newData (JuliaLean.base.int.lit .u8 0)
    let data ← s.convertData newData
    let current ← a.get ref
    a.set ref { current with data }
    let current ← a.get ref
    a.set ref { current with reinit := false }
    let current ← a.get ref
    a.set ref { current with size := n }
  else if JuliaLean.base.int.lt n currentSize then
    if JuliaLean.base.int.lt (JuliaLean.base.int.add n offset) (← liftIO (source_translate_seek_position io io.mark)) then
      let current ← a.get ref
      a.set ref { current with mark := JuliaLean.base.int.lit .i64 (-1) }
    let current ← a.get ref
    a.set ref { current with size := JuliaLean.base.int.add n offset }
    let current ← a.get ref
    a.set ref { current with
      ptr := JuliaLean.base.int.jmin current.ptr (JuliaLean.base.int.add (JuliaLean.base.int.add n offset) one) }
  else if JuliaLean.base.int.lt currentSize n then
    if JuliaLean.base.int.lt io.maxsize (JuliaLean.base.int.add n offset) then
      let _ ← source_compact a s ref
      pure ()
    let current ← a.get ref
    let _ ← source_resize a s ref (JuliaLean.base.int.add n (fieldsOffset current)) false
    let current ← a.get ref
    let data := current.data
    let first := JuliaLean.base.int.add current.size one
    let current ← a.get ref
    let length ← s.length current.data
    let current ← a.get ref
    let last ← s.minimumLength length (JuliaLean.base.int.add n (fieldsOffset current))
    s.fillView data first last (JuliaLean.base.int.lit .u8 0)
    let current ← a.get ref
    let length ← s.length current.data
    let current ← a.get ref
    let last ← s.minimumLength length (JuliaLean.base.int.add n (fieldsOffset current))
    let size ← s.boundToInt last
    let current ← a.get ref
    a.set ref { current with size := size }
  pure ref

/--
Julia source: base/iobuffer.jl:691-691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eof(io::GenericIOBuffer) = (io.ptr - 1 >= io.size)
```
-/
def source_eof (io : BufferState) : Bool := (io.ptr - i 1).val ≥ io.size.val

/--
Julia source: base/iobuffer.jl:693-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function closewrite(io::GenericIOBuffer)
    io.writable = false
    nothing
end
```
-/
def source_closewrite : M Unit := modify fun io => { io with writable := false }

/--
Julia source: base/iobuffer.jl:698-711 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function close(io::GenericIOBuffer{T}) where T
    if io.writable && !io.reinit
        _resize!(io, 0, true)
    end
    io.readable = false
    io.writable = false
    io.seekable = false
    io.size = 0
    io.maxsize = 0
    io.ptr = 1
    io.mark = -1
    io.offset_or_compacted = -get_compacted(io)
    nothing
end
```
-/
def source_close {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData : Type}
    (a : Access m R D) (s : Storage m R D NewData) (ref : R) : m Unit := do
  let io ← a.get ref
  if io.writable && !io.reinit then
    let _ ← source_resize a s ref zero true
    pure ()
  let current ← a.get ref
  a.set ref { current with
    readable := false
    writable := false
    seekable := false
    size := zero
    maxsize := zero
    ptr := one
    mark := JuliaLean.base.int.lit .i64 (-1)
    offset := JuliaLean.base.int.neg_int (fieldsCompacted current) }

/--
Julia source: base/iobuffer.jl:713-713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isopen(io::GenericIOBuffer) = io.readable || io.writable || io.seekable || bytesavailable(io) > 0
```
-/
def source_isopen (bytesAvailable : BufferState → I) (io : BufferState) : Bool :=
  io.readable || io.writable || io.seekable || (bytesAvailable io).val > 0



/--
Julia source: base/iobuffer.jl:731-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function take!(io::GenericIOBuffer)
    io.mark = -1
    if io.seekable
        # If the buffer is seekable, then the previously consumed bytes from 1:ptr-1
        # must still be output, as they are not truly gone.
        # Hence, we output all bytes from 1:io.size
        offset = get_offset(io)
        nbytes = io.size - offset
        data = copyto!(StringVector(nbytes), 1, io.data, offset + 1, nbytes)
    else
        # Else, if not seekable, bytes from 1:ptr-1 are truly gone and should not
        # be output. Hence, we output `bytesavailable`, which is ptr:size
        nbytes = bytesavailable(io)
        data = read!(io, StringVector(nbytes))
    end
    if io.writable
        io.reinit = true
        io.ptr = 1
        io.size = 0
        io.offset_or_compacted = 0
    end
    return data
end
```
-/
def source_take_generic {m : Type → Type} [Monad m] {R D Vector : Type}
    (a : Access m R D) (allocate : I → m Vector)
    (copyto : Vector → I → D → I → I → m Vector) (readInto : R → Vector → m Vector)
    (ref : R) : m Vector := do
  let io ← a.get ref
  a.set ref { io with mark := JuliaLean.base.int.lit .i64 (-1) }
  let io ← a.get ref
  let data ← if io.seekable then do
      let offset := fieldsOffset io
      let count := JuliaLean.base.int.sub io.size offset
      copyto (← allocate count) one io.data (JuliaLean.base.int.add offset one) count
    else readInto ref (← allocate (fieldsBytesavailable io))
  let current ← a.get ref
  if current.writable then
    a.set ref { current with reinit := true, ptr := one, size := zero, offset := zero }
  pure data

/--
Julia source: base/iobuffer.jl:758-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function take!(io::IOBuffer)
    io.mark = -1
    if io.seekable
        nbytes = filesize(io)
        if nbytes == 0 || io.reinit
            data = StringVector(0)
        elseif io.writable
            data = wrap(Array, memoryref(io.data, get_offset(io) + 1), nbytes)
        else
            data = copyto!(StringVector(nbytes), 1, io.data, get_offset(io) + 1, nbytes)
        end
    else
        nbytes = bytesavailable(io)
        if nbytes == 0
            data = StringVector(0)
        elseif io.writable
            data = wrap(Array, memoryref(io.data, io.ptr), nbytes)
        else
            error("Unreachable IOBuffer state")
        end
    end
    if io.writable
        io.reinit = true
        io.ptr = 1
        io.size = 0
        io.offset_or_compacted = 0
    end
    return data
end
```
-/
def source_take_IOBuffer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R Memory Vector : Type}
    (a : Access m R Memory) (allocate : I → m Vector)
    (wrap : Memory → I → I → m Vector)
    (copyto : Vector → I → Memory → I → I → m Vector) (ref : R) : m Vector := do
  let io ← a.get ref
  a.set ref { io with mark := JuliaLean.base.int.lit .i64 (-1) }
  let io ← a.get ref
  let data ← if io.seekable then do
      let count := fieldsFilesize io
      if JuliaLean.base.int.eq_int count zero || io.reinit then allocate zero
      else if io.writable then wrap io.data (JuliaLean.base.int.add (fieldsOffset io) one) count
      else copyto (← allocate count) one io.data (JuliaLean.base.int.add (fieldsOffset io) one) count
    else do
      let count := fieldsBytesavailable io
      if JuliaLean.base.int.eq_int count zero then allocate zero
      else if io.writable then wrap io.data io.ptr count
      else throw (.errorException "Unreachable IOBuffer state")
  let current ← a.get ref
  if current.writable then
    a.set ref { current with reinit := true, ptr := one, size := zero, offset := zero }
  pure data

/--
Julia source: base/iobuffer.jl:795-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_takestring!(io::IOBuffer)
    used_span = get_used_span(io)
    nbytes = length(used_span)
    from = first(used_span)
    isempty(used_span) && return ""
    # The C function can only copy from the start of the memory.
    # Fortunately, in most cases, the offset will be zero.
    return if isone(from)
        ccall(:jl_genericmemory_to_string, Ref{String}, (Any, Int), io.data, nbytes)
    else
        mem = StringMemory(nbytes % UInt)
        unsafe_copyto!(mem, 1, io.data, from, nbytes)
        unsafe_takestring(mem)
    end
end
```
-/
def source_unsafe_takestring {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R Memory StringRef : Type} (a : Access m R Memory)
    (spanLength : I → I → m I) (spanEmpty : I → I → m Bool)
    (emptyString : m StringRef) (memoryToString : Memory → I → m StringRef)
    (allocate : U → m Memory) (copy : Memory → I → Memory → I → I → m Unit)
    (takeMemory : Memory → m StringRef) (ref : R) : m StringRef := do
  let io ← a.get ref
  let (first, last) ← liftIO (source_get_used_span io)
  let count ← spanLength first last
  if ← spanEmpty first last then return (← emptyString)
  if ← isoneInt first then memoryToString io.data count
  else
    let memory ← allocate (JuliaLean.base.int.remT .u64 count)
    copy memory one io.data first count
    takeMemory memory

/--
Julia source: base/iobuffer.jl:835-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function takestring!(io::IOBuffer)
    # If the buffer has been used up and needs to be replaced, there are no bytes, and
    # we can return an empty string without interacting with the buffer at all.
    io.reinit && return ""

    # If the iobuffer is writable, taking will remove the buffer from `io`.
    # So, we reset the iobuffer, and directly unsafe takestring.
    return if io.writable
        s = unsafe_takestring!(io)
        io.reinit = true
        io.mark = -1
        io.ptr = 1
        io.size = 0
        io.offset_or_compacted = 0
        s
    else
        # If the buffer is not writable, taking will NOT remove the buffer,
        # so if we just converted the buffer to a string, garbage collecting
        # the string would free the memory underneath the iobuffer
        used_span = get_used_span(io)
        mem = StringMemory(length(used_span))
        unsafe_copyto!(mem, 1, io.data, first(used_span), length(used_span))
        unsafe_takestring(mem)
    end
end
```
-/
def source_takestring_IOBuffer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R Memory StringRef : Type} (a : Access m R Memory)
    (spanLength : I → I → m I) (spanEmpty : I → I → m Bool)
    (emptyString : m StringRef) (memoryToString : Memory → I → m StringRef)
    (allocateUInt : U → m Memory) (allocateInt : I → m Memory)
    (copy : Memory → I → Memory → I → I → m Unit)
    (takeMemory : Memory → m StringRef) (ref : R) : m StringRef := do
  let io ← a.get ref
  if io.reinit then return (← emptyString)
  if io.writable then
    let string ← source_unsafe_takestring a spanLength spanEmpty emptyString memoryToString
      allocateUInt copy takeMemory ref
    let current ← a.get ref
    a.set ref { current with
      reinit := true
      mark := JuliaLean.base.int.lit .i64 (-1)
      ptr := one
      size := zero
      offset := zero }
    pure string
  else
    let (first, last) ← liftIO (source_get_used_span io)
    let memory ← allocateInt (← spanLength first last)
    copy memory one io.data first (← spanLength first last)
    takeMemory memory

/--
Julia source: base/iobuffer.jl:862-862 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
takestring!(io::GenericIOBuffer) = String(take!(io))
```
-/
def source_takestring_generic {m : Type → Type} [Monad m] {R Array StringRef : Type}
    (take : R → m Array) (convertString : Array → m StringRef) (ref : R) : m StringRef := do
  convertString (← take ref)

/--
Julia source: base/iobuffer.jl:876-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _unsafe_take!(io::IOBuffer)
    offset = get_offset(io)
    mem = if io.size == offset
        memoryref(Memory{UInt8}())
    else
        memoryref(io.data, offset + 1)
    end
    wrap(Array, mem, io.size - offset)
end
```
-/
def source_unsafe_take {m : Type → Type} [Monad m] {R Memory Ref Vector : Type}
    (a : Access m R Memory) (emptyMemory : m Memory) (memoryref : Memory → I → m Ref)
    (wrapCheck : Ref → List I → m Ref) (newArray : Ref → List I → m Vector)
    (toInt : I → m I) (ref : R) : m Vector := do
  let io ← a.get ref
  let offset := fieldsOffset io
  let memory ← if JuliaLean.base.int.eq_int io.size offset then
      memoryref (← emptyMemory) one
    else memoryref io.data (JuliaLean.base.int.add offset one)
  JuliaLean.base.array.wrapRefLength toInt wrapCheck newArray memory
    (JuliaLean.base.int.sub io.size offset)

/--
Julia source: base/iobuffer.jl:886-897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(to::IO, from::GenericIOBuffer)
    # This would cause an infinite loop, as it should read until the end, but more
    # data is being written into it continuously.
    if to === from
        throw(ArgumentError("Writing all content fron an IOBuffer into itself in invalid"))
    else
        from.readable || _throw_not_readable()
        written = write(to, view(from.data, from.ptr:from.size))
        from.ptr = from.size + 1
    end
    return written
end
```
-/
def source_write_buffer_to_IO {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D Out View : Type}
    (a : Access m R D) (identical : Out → R → m Bool)
    (view : D → I → I → m View) (write : Out → View → m I) (out : Out) (input : R) : m I := do
  if ← identical out input then
    throw (.jl (.argumentError "Writing all content fron an IOBuffer into itself in invalid"))
  let io ← a.get input
  if !io.readable then liftIO JuliaLean.base.iobuffer.source_throw_not_readable
  let written ← write out (← view io.data io.ptr io.size)
  let current ← a.get input
  a.set input { current with ptr := JuliaLean.base.int.add current.size one }
  pure written

/--
Julia source: base/iobuffer.jl:902-921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_write(to::GenericIOBuffer, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)
    precheck_cancel_arg(cancel)
    ensureroom(to, nb)
    size = to.size
    append = to.append
    ptr = append ? size+1 : to.ptr
    data = to.data
    start_offset = ptr - 1
    to_write = max(0, min(nb, (min(Int(length(data))::Int - start_offset, to.maxsize - (start_offset - get_offset(to)))) % UInt) % Int)
    # Dispatch based on the type of data, to possibly allow using memcpy
    _unsafe_write(data, p, ptr, to_write % UInt)
    # Update to.size only if the ptr has advanced to higher than
    # the previous size. Otherwise, we just overwrote existing data
    to.size = max(size, start_offset + to_write)
    # If to.append, we only update size, not ptr.
    if !append
        to.ptr = ptr + to_write
    end
    return to_write
end
```
-/
def source_unsafe_write {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R D NewData P Cancel StoreResult : Type}
    (a : Access m R D) (s : Storage m R D NewData) (precheck : Cancel → m Unit)
    (store : D → P → I → U → m StoreResult)
    (ref : R) (pointer : P) (count : U) (cancel : Cancel) : m I := do
  precheck cancel
  let _ ← source_ensureroom a s ref count
  let io ← a.get ref
  let size := io.size
  let append := io.append
  let ptr := if append then JuliaLean.base.int.add size one else io.ptr
  let data := io.data
  let start := JuliaLean.base.int.sub ptr one
  let length ← s.lengthToInt (← s.length data)
  let current ← a.get ref
  let capacity := JuliaLean.base.int.jmin (JuliaLean.base.int.sub length start)
    (JuliaLean.base.int.sub current.maxsize (JuliaLean.base.int.sub start (fieldsOffset current)))
  let count := JuliaLean.base.int.jmax zero (JuliaLean.base.int.remT .i64
    (JuliaLean.base.int.jmin count (JuliaLean.base.int.remT .u64 capacity)))
  let _ ← store data pointer ptr (JuliaLean.base.int.remT .u64 count)
  let current ← a.get ref
  a.set ref { current with size := JuliaLean.base.int.jmax size (JuliaLean.base.int.add start count) }
  if !append then
    let current ← a.get ref
    a.set ref { current with ptr := JuliaLean.base.int.add ptr count }
  pure count

/--
Julia source: base/iobuffer.jl:923-928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _unsafe_write(data::AbstractVector{UInt8}, p::Ptr{UInt8}, from::Int, nb::UInt)
    for i in 0:nb-1
        data[from + i] = unsafe_load(p)
        p += 1
    end
end
```
-/
def source_unsafe_write_vector {m : Type → Type} [Monad m] {D P : Type}
    (setindex : D → Byte → U → m Unit) (load : P → m Byte) (advance : P → m P)
    (data : D) (pointer : P) (start : I) (count : U) : m Unit := do
  let mut pointer := pointer
  let lastIndex := JuliaLean.base.int.binop JuliaLean.base.int.sub count one
  for k in List.range (lastIndex.val.toNat + 1) do
    let index := JuliaLean.base.int.binop JuliaLean.base.int.add start
      (JuliaLean.base.int.lit .u64 k)
    setindex data (← load pointer) index
    pointer ← advance pointer

/--
Julia source: base/iobuffer.jl:930-946 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _unsafe_write(data::MutableDenseArrayType{UInt8}, p::Ptr{UInt8}, from::Int, nb::UInt)
    # Calling `unsafe_copyto!` is very efficient for large arrays, but has some overhead
    # for small (< 5 bytes) arrays.
    # Since a common use case of IOBuffer is to construct strings incrementally, often
    # one char at a time, it's crucial to be fast in the case of small arrays.
    # This optimization only gives a minor 10% speed boost in the best case.
    if nb < 5
        @inbounds for i in UInt(1):nb
            data[from + (i % Int) - 1] = unsafe_load(p, i)
        end
    else
        GC.@preserve data begin
            ptr = Ptr{UInt8}(pointer(data, from))::Ptr{UInt8}
            @inline unsafe_copyto!(ptr, p, nb)
        end
    end
end
```
-/
def source_unsafe_write_dense {m : Type → Type} [Monad m] {D P : Type}
    (setindex : D → Byte → I → m Unit) (load : P → U → m Byte)
    (pointer : D → I → m P) (copy : P → P → U → m P)
    (data : D) (src : P) (start : I) (count : U) : m (Unit ⊕ P) := do
  if JuliaLean.base.int.lt count (JuliaLean.base.int.lit .i64 5) then
    for k in List.range count.val.toNat do
      let index := JuliaLean.base.int.lit .u64 (k + 1)
      let destination := JuliaLean.base.int.sub
        (JuliaLean.base.int.add start (JuliaLean.base.int.remT .i64 index)) one
      setindex data (← load src index) destination
    pure (.inl ())
  else pure (.inr (← copy (← pointer data start) src count))

/--
Julia source: base/iobuffer.jl:948-963 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function write(to::GenericIOBuffer, a::UInt8)
    ensureroom(to, UInt(1))
    ptr = (to.append ? to.size+1 : to.ptr)
    # We have just ensured there is room for 1 byte, EXCEPT if we were to exceed
    # maxsize. So, we just need to check that here.
    if ptr - get_offset(to) > to.maxsize
        return 0
    else
        to.data[ptr] = a
    end
    to.size = max(to.size, ptr)
    if !to.append
        to.ptr += 1
    end
    return sizeof(UInt8)
end
```
-/
def source_write_uint8 {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D NewData : Type}
    (a : Access m R D) (s : Storage m R D NewData) (setindex : D → I → Byte → m Unit)
    (ref : R) (byte : Byte) : m I := do
  let _ ← source_ensureroom a s ref (JuliaLean.base.int.lit .u64 1)
  let io ← a.get ref
  let ptr := if io.append then JuliaLean.base.int.add io.size one else io.ptr
  if JuliaLean.base.int.lt io.maxsize (JuliaLean.base.int.sub ptr (fieldsOffset io)) then return zero
  setindex io.data ptr byte
  let current ← a.get ref
  a.set ref { current with size := JuliaLean.base.int.jmax current.size ptr }
  let current ← a.get ref
  if !current.append then a.set ref { current with ptr := JuliaLean.base.int.add current.ptr one }
  pure one

/--
Julia source: base/iobuffer.jl:967-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readbytes!(io::GenericIOBuffer, b::MutableDenseArrayType{UInt8}, nb::Int)
    io.readable || _throw_not_readable()
    to_read = min(nb, bytesavailable(io))
    if length(b) < to_read
        resize!(b, to_read)
    end
    checkbounds(b, 1:to_read)
    GC.@preserve b unsafe_read(io, pointer(b), to_read)
    to_read
end
```
-/
def source_readbytes_int {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D Array : Type}
    (a : Access m R D) (length : Array → m I) (resize : Array → I → m Unit)
    (checkBounds : Array → I → m Unit) (pointer : Array → m (JuliaLean.base.pointer.Ptr Byte))
    (readBang : JuliaLean.base.pointer.Ptr Byte → D → I → U → m Unit)
    (ref : R) (dest : Array) (requested : I) : m I := do
  let io ← a.get ref
  if !io.readable then liftIO JuliaLean.base.iobuffer.source_throw_not_readable
  let count := JuliaLean.base.int.jmin requested (fieldsBytesavailable io)
  if JuliaLean.base.int.lt (← length dest) count then resize dest count
  checkBounds dest count
  unsafeReadInt a readBang ref (← pointer dest) count
  pure count

/--
Julia source: base/iobuffer.jl:965-965 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readbytes!(io::GenericIOBuffer, b::MutableDenseArrayType{UInt8}, nb=length(b)) = readbytes!(io, b, Int(nb)::Int)
```
-/
def source_readbytes_default {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {R D Array N : Type}
    (a : Access m R D) (length : Array → m N) (toInt : N → m I)
    (lengthInt : Array → m I) (resize : Array → I → m Unit)
    (checkBounds : Array → I → m Unit) (pointer : Array → m (JuliaLean.base.pointer.Ptr Byte))
    (readBang : JuliaLean.base.pointer.Ptr Byte → D → I → U → m Unit)
    (ref : R) (dest : Array) (requested : Option N) : m I := do
  let n ← match requested with
    | some n => pure n
    | none => length dest
  source_readbytes_int a lengthInt resize checkBounds pointer readBang ref dest (← toInt n)

/--
Julia source: base/iobuffer.jl:977-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::GenericIOBuffer) = read!(io, StringVector(bytesavailable(io)))
```
-/
def source_read_all {m : Type → Type} [Monad m] {R D Array : Type}
    (a : Access m R D) (allocate : I → m Array) (readInto : R → Array → m Array) (ref : R) : m Array := do
  let io ← a.get ref
  readInto ref (← allocate (fieldsBytesavailable io))

/--
Julia source: base/iobuffer.jl:980-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readavailable(io::GenericIOBuffer) = read(io)
```
-/
def source_readavailable {m : Type → Type} [Monad m] {R D Array : Type}
    (a : Access m R D) (allocate : I → m Array) (readInto : R → Array → m Array) (ref : R) : m Array :=
  source_read_all a allocate readInto ref

/--
Julia source: base/iobuffer.jl:982-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::GenericIOBuffer, nb::Integer) = read!(io, StringVector(min(nb, bytesavailable(io))))
```
-/
def source_read_n {m : Type → Type} [Monad m] {R D Array N Count : Type}
    (a : Access m R D) (minCount : N → I → m Count) (allocate : Count → m Array)
    (readInto : R → Array → m Array) (ref : R) (count : N) : m Array := do
  let io ← a.get ref
  readInto ref (← allocate (← minCount count (fieldsBytesavailable io)))

/--
Julia source: base/iobuffer.jl:984-986 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function occursin(delim::UInt8, buf::GenericIOBuffer)
    return in(delim, view(buf.data, buf.ptr:buf.size))
end
```
-/
def source_occursin {m : Type → Type} [Monad m] {R D View Result : Type}
    (a : Access m R D) (view : D → I → I → m View)
    (member : Byte → View → m Result) (delimiter : Byte) (ref : R) : m Result := do
  let io ← a.get ref
  member delimiter (← view io.data io.ptr io.size)

/--
Julia source: base/iobuffer.jl:993-1008 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyuntil(out::IO, io::GenericIOBuffer, delim::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    data = view(io.data, io.ptr:io.size)
    # note: findfirst + copyto! is much faster than a single loop
    #       except for nout ≲ 20.  A single loop is 2x faster for nout=5.
    nout = nread = something(findfirst(==(delim), data), length(data))
    if !keep && nout > 0 && data[nout] == delim
        nout -= 1
    end
    if cancel === DEFAULT_CANCEL
        write(out, view(io.data, io.ptr:io.ptr+nout-1))
    else
        write(out, view(io.data, io.ptr:io.ptr+nout-1); cancel)
    end
    io.ptr += nread
    return out
end
```
-/
def source_copyuntil {m : Type → Type} [Monad m] {R D Out View Cancel : Type}
    (a : Access m R D) (view : D → I → I → m View)
    (findfirst : Byte → View → m (Option I)) (length : View → m I)
    (getindex : View → I → m Byte) (isDefault : Cancel → m Bool)
    (writeDefault : Out → View → m Unit) (writeToken : Out → View → Cancel → m Unit)
    (out : Out) (ref : R) (delimiter : Byte) (keep : Bool) (cancel : Cancel) : m Out := do
  let io ← a.get ref
  let data ← view io.data io.ptr io.size
  let found ← findfirst delimiter data
  let fallback ← length data
  let count := somethingIndex found fallback
  let mut output := count
  if !keep then
    if JuliaLean.base.int.lt zero output then
      if JuliaLean.base.int.eq_int (← getindex data output) delimiter then
        output := JuliaLean.base.int.sub output one
  let current ← a.get ref
  let bytes ← view current.data current.ptr
    (JuliaLean.base.int.sub (JuliaLean.base.int.add current.ptr output) one)
  if ← isDefault cancel then writeDefault out bytes else writeToken out bytes cancel
  let current ← a.get ref
  a.set ref { current with ptr := JuliaLean.base.int.add current.ptr count }
  pure out

/--
Julia source: base/iobuffer.jl:1010-1055 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyline(out::GenericIOBuffer, s::IO; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = check_cancel_arg(cancel)
    # If the data is copied into the middle of the buffer of `out` instead of appended to the end,
    # and !keep, and the line copied ends with \r\n, then the copyuntil (even if keep=false)
    # will overwrite one too many bytes with the new \r byte.
    # Work around this by making a new temporary buffer.
    # Could perhaps be done better
    if !out.append && out.ptr < out.size + 1
        newbuf = IOBuffer()
        cancel === DEFAULT_CANCEL ? copyuntil(newbuf, s, 0x0a; keep=true) :
                                    copyuntil(newbuf, s, 0x0a; keep=true, cancel=tok)
        v = take!(newbuf)
        # Remove \r\n or \n if present
        if !keep
            if length(v) > 1 && last(v) == UInt8('\n')
                pop!(v)
            end
            if length(v) > 1 && last(v) == UInt8('\r')
                pop!(v)
            end
        end
        # `tok` is resolved above: the write to `out` runs under it (or its
        # explicit shield), not the ambient scope
        write(out, v; cancel=tok)
        return out
    else
        # Else, we can just copy the data directly into the buffer, and then
        # subtract the last one or two bytes depending on `keep`.
        cancel === DEFAULT_CANCEL ? copyuntil(out, s, 0x0a; keep=true) :
                                    copyuntil(out, s, 0x0a; keep=true, cancel=tok)
        line = out.data
        i = out.size
        if keep || i == out.offset_or_compacted || line[i] != 0x0a
            return out
        elseif i < 2 || line[i-1] != 0x0d
            i -= 1
        else
            i -= 2
        end
        out.size = i
        if !out.append
            out.ptr = i+1
        end
        return out
    end
end
```
-/
def source_copyline_buffer {m : Type → Type} [Monad m] {R D Stream Cancel Vector : Type}
    (a : Access m R D) (isDefault : Cancel → m Bool) (checkCancel : Cancel → m Cancel)
    (newBuffer : m R) (copyDefault : R → Stream → Byte → Bool → m Unit)
    (copyToken : R → Stream → Byte → Bool → Cancel → m Unit)
    (take : R → m Vector) (length : Vector → m I) (last : Vector → m Byte)
    (pop : Vector → m Unit) (write : R → Vector → Cancel → m Unit)
    (getByte : D → I → m Byte) (out : R) (stream : Stream) (keep : Bool) (cancel : Cancel) : m R := do
  let token ← checkCancel cancel
  let before ← a.get out
  if !before.append && JuliaLean.base.int.lt before.ptr (JuliaLean.base.int.add before.size one) then
    let temporary ← newBuffer
    if ← isDefault cancel then copyDefault temporary stream (JuliaLean.base.int.lit .u8 10) true
    else copyToken temporary stream (JuliaLean.base.int.lit .u8 10) true token
    let bytes ← take temporary
    if !keep then
      if JuliaLean.base.int.lt one (← length bytes) then
        if JuliaLean.base.int.eq_int (← last bytes) (JuliaLean.base.int.lit .u8 10) then pop bytes
    if !keep then
      if JuliaLean.base.int.lt one (← length bytes) then
        if JuliaLean.base.int.eq_int (← last bytes) (JuliaLean.base.int.lit .u8 13) then pop bytes
    write out bytes token
    pure out
  else
    if ← isDefault cancel then copyDefault out stream (JuliaLean.base.int.lit .u8 10) true
    else copyToken out stream (JuliaLean.base.int.lit .u8 10) true token
    let current ← a.get out
    let mut index := current.size
    if keep || JuliaLean.base.int.eq_int index current.offset then return out
    if !(JuliaLean.base.int.eq_int (← getByte current.data index) (JuliaLean.base.int.lit .u8 10)) then return out
    if JuliaLean.base.int.lt index (JuliaLean.base.int.lit .i64 2) then
      index := JuliaLean.base.int.sub index one
    else if JuliaLean.base.int.eq_int
        (← getByte current.data (JuliaLean.base.int.sub index one)) (JuliaLean.base.int.lit .u8 13) then
      index := JuliaLean.base.int.sub index (JuliaLean.base.int.lit .i64 2)
    else index := JuliaLean.base.int.sub index one
    let latest ← a.get out
    a.set out { latest with
      size := index
      ptr := if latest.append then latest.ptr else JuliaLean.base.int.add index one }
    pure out

/--
Julia source: base/iobuffer.jl:1057-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copyline(out::IO, io::GenericIOBuffer; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    data = view(io.data, io.ptr:io.size)
    # note: findfirst + copyto! is much faster than a single loop
    #       except for nout ≲ 20.  A single loop is 2x faster for nout=5.
    nout = nread = something(findfirst(==(0x0a), data), length(data))::Int
    # Remove the 0x0a (newline) if not keep, and also remove the 0x0d (\r) if it is there
    if !keep && nout > 0 && data[nout] == 0x0a
        nout -= 1
        nout > 0 && data[nout] == 0x0d && (nout -= 1)
    end
    if cancel === DEFAULT_CANCEL
        write(out, view(io.data, io.ptr:io.ptr+nout-1))
    else
        write(out, view(io.data, io.ptr:io.ptr+nout-1); cancel)
    end
    io.ptr += nread
    return out
end
```
-/
def source_copyline_read {m : Type → Type} [Monad m] {R D View Out Cancel : Type}
    (a : Access m R D) (view : D → I → I → m View)
    (findFirst : Byte → View → m (Option I)) (length : View → m I)
    (getByte : View → I → m Byte) (isDefault : Cancel → Bool)
    (writeDefault : Out → View → m Unit) (writeToken : Out → View → Cancel → m Unit)
    (out : Out) (ref : R) (keep : Bool) (cancel : Cancel) : m Out := do
  let io ← a.get ref
  let data ← view io.data io.ptr io.size
  let found ← findFirst (JuliaLean.base.int.lit .u8 10) data
  let fallback ← length data
  let read := somethingIndex found fallback
  let mut written := read
  if !keep && JuliaLean.base.int.lt zero written then
    if JuliaLean.base.int.eq_int (← getByte data written) (JuliaLean.base.int.lit .u8 10) then
      written := JuliaLean.base.int.sub written one
      if JuliaLean.base.int.lt zero written then
        if JuliaLean.base.int.eq_int (← getByte data written) (JuliaLean.base.int.lit .u8 13) then
          written := JuliaLean.base.int.sub written one
  let current ← a.get ref
  let last := JuliaLean.base.int.sub (JuliaLean.base.int.add current.ptr written) one
  let bytes ← view current.data current.ptr last
  if isDefault cancel then writeDefault out bytes else writeToken out bytes cancel
  let current ← a.get ref
  a.set ref { current with ptr := JuliaLean.base.int.add current.ptr read }
  pure out

/--
Julia source: base/iobuffer.jl:1079-1079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyline(out::IO, io::GenericIOBuffer; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL) = _copyline(out, io; keep, cancel)
```
-/
def source_copyline_IO {m : Type → Type} [Monad m] {R D View Out Cancel : Type}
    (a : Access m R D) (view : D → I → I → m View)
    (findFirst : Byte → View → m (Option I)) (length : View → m I)
    (getByte : View → I → m Byte) (isDefault : Cancel → Bool)
    (writeDefault : Out → View → m Unit) (writeToken : Out → View → Cancel → m Unit)
    (out : Out) (ref : R) (keep : Bool) (cancel : Cancel) : m Out :=
  source_copyline_read a view findFirst length getByte isDefault writeDefault writeToken
    out ref keep cancel

/--
Julia source: base/iobuffer.jl:1080-1080 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyline(out::GenericIOBuffer, io::GenericIOBuffer; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL) = _copyline(out, io; keep, cancel)
```
-/
def source_copyline_buffer_buffer {m : Type → Type} [Monad m] {R D View Out Cancel : Type}
    (a : Access m R D) (view : D → I → I → m View)
    (findFirst : Byte → View → m (Option I)) (length : View → m I)
    (getByte : View → I → m Byte) (isDefault : Cancel → Bool)
    (writeDefault : Out → View → m Unit) (writeToken : Out → View → Cancel → m Unit)
    (out : Out) (ref : R) (keep : Bool) (cancel : Cancel) : m Out :=
  source_copyline_read a view findFirst length getByte isDefault writeDefault writeToken
    out ref keep cancel

/--
Julia source: base/iobuffer.jl:1084-1092 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _crc32c(io::IOBuffer, nb::Integer, crc::UInt32=0x00000000)
    nb < 0 && throw(ArgumentError("number of bytes to checksum must be ≥ 0, got $nb"))
    io.readable || _throw_not_readable()
    n = min(nb, bytesavailable(io))
    n == 0 && return crc
    crc = GC.@preserve io unsafe_crc32c(pointer(io.data, io.ptr), n, crc)
    io.ptr += n
    return crc
end
```
-/
def source_crc32c_bytes {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R D N Count Sum P : Type} (a : Access m R D) (c : CrcCalls m D N Count Sum P)
    (preserve : R → (Unit → m UInt32) → m UInt32)
    (ref : R) (requested : N) (seed : Option UInt32) : m UInt32 := do
  if ← c.negative requested then
    let value ← c.showCount requested
    throw (.jl (.argumentError ("number of bytes to checksum must be ≥ 0, got " ++ value)))
  let io ← a.get ref
  if !io.readable then liftIO source_throw_not_readable
  let count ← c.minimum requested (fieldsBytesavailable io)
  let crc := seed.getD 0
  if ← c.iszero count then return crc
  let crc ← preserve ref (fun _ => do
    let current ← a.get ref
    c.unsafeCrc (← c.pointer current.data current.ptr) count crc)
  let current ← a.get ref
  let next ← c.toNativePointer (← c.addPointer current.ptr count)
  let current ← a.get ref
  a.set ref { current with ptr := next }
  pure crc

abbrev crcCounted := @source_crc32c_bytes

/--
Julia source: base/iobuffer.jl:1093-1093 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(io::IOBuffer, crc::UInt32=0x00000000) = _crc32c(io, bytesavailable(io), crc)
```
-/
def source_crc32c_default {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {R D Count Sum P : Type} (a : Access m R D) (c : CrcCalls m D I Count Sum P)
    (preserve : R → (Unit → m UInt32) → m UInt32)
    (ref : R) (seed : Option UInt32) : m UInt32 := do
  let io ← a.get ref
  source_crc32c_bytes a c preserve ref (fieldsBytesavailable io) seed

abbrev crcDefault := @source_crc32c_default


def copyModel (similar : List UInt8 → I → Except IOErr (List UInt8)) (b : BufferState) :
    Except IOErr BufferState :=
  source_copy
    (fun buffer count =>
      if buffer.isMemory then stringMemoryBytes count.val
      else similar buffer.data count)
    (fun bytes readable writable seekable append maxsize truncate =>
      genericIOBuffer (if b.isMemory then .mem bytes else .other bytes)
        readable writable seekable append maxsize.val truncate) b

def peekArrayModel (kind : Multibyte)
    (ltoh : (t : IntTy) → JInt t → M (JInt t))
    (full : (kind : Multibyte) → JInt (wordType kind) → M (valueType kind)) :
    M (valueType kind) :=
  source_peek_multibyte bufferAccess
    (fun bytes idx => do
      let b ← lift (getChecked bytes idx)
      pure (JuliaLean.base.int.lit .u8 b.toNat))
    ltoh full () kind

def readUIntModel : M U :=
  source_read_multibyte bufferAccess
    (fun bytes idx => do
      let b ← lift (getChecked bytes idx)
      pure (JuliaLean.base.int.lit .u8 b.toNat))
    (fun _ w => pure w) (fun _ v => pure (bitcastWord _ v)) () .u64

/-- Convert IOBuffer's error representation without discarding its exception kind. -/
def genericIOError : IOErr → JuliaLean.base.io.Error
  | .jl error => .jl error
  | .eofError => .eofError
  | .errorException message => .errorException message
  | .typeError => .foreignError "TypeError" ""
  | .outOfBounds => .foreignError "UB" "unchecked buffer access outside storage"
  | .showError error => .showError error

/-- Run an IOBuffer method in the generic IO world, retaining partial mutations. -/
def liftBufferIO {World Stream A : Type}
    (getBuffer : Stream → JuliaLean.base.io.M World BufferState)
    (setBuffer : Stream → BufferState → JuliaLean.base.io.M World Unit)
    (stream : Stream) (action : M A) : JuliaLean.base.io.M World A := do
  let buffer ← getBuffer stream
  match action.run buffer with
  | .ok value buffer =>
    setBuffer stream buffer
    pure value
  | .error error buffer =>
    setBuffer stream buffer
    throw (genericIOError error)

/-- IOBuffer instantiates the generic IO interface for arbitrary stream handles. -/
def genericIOOps {World Stream : Type}
    (getBuffer : Stream → JuliaLean.base.io.M World BufferState)
    (setBuffer : Stream → BufferState → JuliaLean.base.io.M World Unit) :
    JuliaLean.base.io.Ops World Stream where
  readByte := fun stream => do
    let value ← liftBufferIO getBuffer setBuffer stream readByte
    pure (JInt.wrap .u8 value.toNat)
  writeByte := fun stream value =>
    liftBufferIO getBuffer setBuffer stream (writeByte (UInt8.ofNat value.val.toNat))
  eof := fun stream => do pure (eof (← getBuffer stream))
  bytesavailable := fun stream => do pure (bytesavailable (← getBuffer stream))
  position := fun stream => do pure (position (← getBuffer stream))
  seek := fun stream target => liftBufferIO getBuffer setBuffer stream (seek target)
  seekend := fun stream => liftBufferIO getBuffer setBuffer stream seekend
  getMark := fun stream => do pure (← getBuffer stream).mark
  setMark := fun stream marked => do
    let buffer ← getBuffer stream
    setBuffer stream { buffer with mark := marked }
  isopen := fun stream => do pure (source_isopen bytesavailable (← getBuffer stream))
  close := fun stream => liftBufferIO getBuffer setBuffer stream close
  isreadable := fun stream => do pure (source_isreadable (← getBuffer stream))
  iswritable := fun stream => do pure (source_iswritable (← getBuffer stream))

def singleBufferIOOps : JuliaLean.base.io.Ops BufferState Unit :=
  genericIOOps (fun _ => JuliaLean.base.io.getWorld)
    (fun _ buffer => JuliaLean.base.io.setWorld buffer)
/-!
## Concrete shared-heap IOBuffer bindings
-- placed here to break an import cycle with stream and iostream
-/

/-- Shared object and byte storage. `other` holds the selected Array/Memory runtime state. -/
structure BufferHeap (Ref Data Other : Type) where
  bytes : JuliaLean.base.pointer.ByteHeap
  buffers : List (Ref × Fields Data)
  other : Other

def findBufferFields {m : Type → Type} [Monad m] {Ref Data : Type}
    (sameRef : Ref → Ref → Bool) (ref : Ref) :
    List (Ref × Fields Data) → m (Option (Fields Data))
  | [] => pure none
  | (candidate, fields) :: rest => do
      if sameRef ref candidate then pure (some fields) else findBufferFields sameRef ref rest

def replaceBufferFields {Ref Data : Type} (sameRef : Ref → Ref → Bool) (ref : Ref)
    (fields : Fields Data) :
    List (Ref × Fields Data) → Option (List (Ref × Fields Data))
  | [] => none
  | (candidate, old) :: rest =>
      if sameRef ref candidate then some ((candidate, fields) :: rest)
      else (replaceBufferFields sameRef ref fields rest).map fun next => (candidate, old) :: next

structure ObjectRuntime (m : Type → Type) (Ref Data : Type) where
  sameRef : Ref → Ref → Bool
  allocateObject : Fields Data → m Ref

def bindHeapAccess {m : Type → Type} [Monad m] {Ref Data Other : Type}
    (getHeap : m (BufferHeap Ref Data Other))
    (setHeap : BufferHeap Ref Data Other → m Unit)
    (throwInvalid : {α : Type} → String → m α)
    (calls : ObjectRuntime m Ref Data) : Access m Ref Data where
  get ref := do
    let heap ← getHeap
    match ← findBufferFields calls.sameRef ref heap.buffers with
    | some fields => pure fields
    | none => throwInvalid "reading an invalid IOBuffer reference"
  set ref fields := do
    let heap ← getHeap
    match replaceBufferFields calls.sameRef ref fields heap.buffers with
    | some buffers => setHeap { heap with buffers }
    | none => throwInvalid "writing an invalid IOBuffer reference"
  new fields := do
    let ref ← calls.allocateObject fields
    let heap ← getHeap
    setHeap { heap with buffers := heap.buffers ++ [(ref, fields)] }
    pure ref
  isIOBuffer ref := do
    let heap ← getHeap
    pure (← findBufferFields calls.sameRef ref heap.buffers).isSome

def bindHeapPointerHeap {m : Type → Type} [Monad m] {Ref Data Other : Type}
    (getHeap : m (BufferHeap Ref Data Other))
    (setHeap : BufferHeap Ref Data Other → m Unit) : HeapAccess m where
  get := do pure (← getHeap).bytes
  set bytes := do
    let heap ← getHeap
    setHeap { heap with bytes }

def arrayIOError : JuliaLean.base.array.Error → JuliaLean.base.io.Error
  | .argument msg => .jl (.argumentError msg)
  | .bounds => .jl .boundsError
  | .inexact => .jl (.inexactError "convert")
  | .overflow => .jl (.overflowError "")
  | .divide => .jl .divideError
  | .typeError ctx => .foreignError "TypeError" ctx
  | .dimensionMismatch msg => .foreignError "DimensionMismatch" msg
  | .method name => .jl (.methodError name)
  | .assertion msg => .foreignError "AssertionError" msg
  | .concurrency msg => .errorException msg
  | .thrownNothing => .foreignError "Nothing" ""
  | .undefinedReference => .foreignError "UndefRefError" "access to undefined reference"
  | .showError err => .showError err

def pointerIOError : JuliaLean.base.pointer.PointerError → JuliaLean.base.io.Error
  | .julia e => .jl e
  | .errorException msg => .errorException msg
  | .methodError name => .jl (.methodError name)

namespace IOHeap

scoped instance instMonadExceptOfIOErrIOM {World : Type} :
    MonadExceptOf IOErr (JuliaLean.base.io.M World) where
  throw error := fun world => some (.error (genericIOError error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok res) => some (.ok res)
    | some (.error (err, w)) =>
      match err with
      | .jl e => handler (.jl e) w
      | .eofError => handler .eofError w
      | .errorException msg => handler (.errorException msg) w
      | .showError e => handler (.showError e) w
      | .foreignError "TypeError" _ => handler .typeError w
      | .foreignError "UB" _ => handler .outOfBounds w
      | _ => some (.error (err, w))

scoped instance instMonadExceptOfArrayErrorIOM {World : Type} :
    MonadExceptOf JuliaLean.base.array.Error (JuliaLean.base.io.M World) where
  throw error := fun world => some (.error (arrayIOError error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok res) => some (.ok res)
    | some (.error (err, w)) =>
      match err with
      | .jl .boundsError => handler .bounds w
      | .jl (.argumentError msg) => handler (.argument msg) w
      | .jl (.inexactError _) => handler .inexact w
      | .jl (.overflowError _) => handler .overflow w
      | .jl .divideError => handler .divide w
      | .jl (.methodError name) => handler (.method name) w
      | .foreignError "DimensionMismatch" msg => handler (.dimensionMismatch msg) w
      | .foreignError "UndefRefError" _ => handler .undefinedReference w
      | .foreignError "AssertionError" msg => handler (.assertion msg) w
      | .foreignError "TypeError" ctx => handler (.typeError ctx) w
      | .foreignError "Nothing" _ => handler .thrownNothing w
      | .errorException msg => handler (.concurrency msg) w
      | .showError err => handler (.showError err) w
      | _ => some (.error (err, w))

scoped instance instMonadExceptOfPointerErrorIOM {World : Type} :
    MonadExceptOf JuliaLean.base.pointer.PointerError (JuliaLean.base.io.M World) where
  throw error := fun world => some (.error (pointerIOError error, world))
  tryCatch action handler := fun world =>
    match action world with
    | none => none
    | some (.ok res) => some (.ok res)
    | some (.error (err, w)) =>
      match err with
      | .jl (.methodError name) => handler (.methodError name) w
      | .jl e => handler (.julia e) w
      | .errorException msg => handler (.errorException msg) w
      | _ => some (.error (err, w))

end IOHeap
def byteCodec : JuliaLean.base.pointer.ByteCodec Byte where
  elementSize := one
  size_nonnegative := by decide
  encode byte := [byte]
  decode bytes := bytes.getD 0 (JInt.wrap .u8 0)
  encode_length _ := rfl
  decode_encode _ := rfl

def loadBytePointer {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m]
    (heap : HeapAccess m)
    (pointer : JuliaLean.base.pointer.Ptr Byte) (index : U) : m Byte :=
  pointerLoad heap byteCodec pointer index

def storeBytePointer {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.pointer.PointerError m]
    (heap : HeapAccess m)
    (pointer : JuliaLean.base.pointer.Ptr Byte) (value : Byte) (index : U) : m Unit :=
  pointerStore heap byteCodec pointer value index

def copyBytePointer {m : Type → Type} [Monad m]
    (memmove : JuliaLean.base.pointer.Ptr Byte → JuliaLean.base.pointer.Ptr Byte → U → m Unit)
    (destination source : JuliaLean.base.pointer.Ptr Byte) (count : U) :
    m (JuliaLean.base.pointer.Ptr Byte) :=
  pointerCopy memmove destination source count

def setMemoryByte {m : Type → Type} [Monad m] {Memory P : Type}
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (memory : Memory) (value : Byte) (index : I) : m Unit := do
  let _ ← JuliaLean.base.genericmemory.setindexMemoryRaw memoryOps false memory value index
  pure ()

def setArrayByte {m : Type → Type} [Monad m] {Data Memory P : Type}
    (arrayOps : JuliaLean.base.array.Storage m Data Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (checkBounds : Data → I → m Unit) (data : Data) (value : Byte) (index : I) : m Unit := do
  let reference ← arrayOps.ref data
  let _ ← JuliaLean.base.array.setindexTyped checkBounds
    (fun _ i boundsChecking => memoryOps.memoryrefNew reference i boundsChecking)
    (fun ref byte boundsChecking => memoryOps.memoryrefSet ref byte .notAtomic boundsChecking)
    data value index
  pure ()

def vectorBounds {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.array.Error m]
    {Data Memory P : Type}
    (arrayOps : JuliaLean.base.array.Storage m Data Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (data : Data) (index : I) : m Unit := do
  if !(JuliaLean.base.abstractarray.checkindexOneTo (← arrayOps.length data) index) then
    throw .bounds

def getArrayByte {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Data Memory P : Type}
    (arrayOps : JuliaLean.base.array.Storage m Data Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (data : Data) (index : I) : m Byte := do
  vectorBounds arrayOps data index
  let reference ← arrayOps.ref data
  let reference ← arrayOps.shiftref reference
    (JuliaLean.base.int.sub index one)
  memoryOps.getindex (arrayOps.memory reference) (arrayOps.offset reference)

def copyVector {m : Type → Type} [Monad m] [MonadExceptOf JuliaLean.base.array.Error m]
    {Data Memory P : Type}
    (arrayOps : JuliaLean.base.array.Storage m Data Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (destination : Data) (destinationIndex : I) (source : Data) (sourceIndex count : I) :
    m Data :=
  JuliaLean.base.array.copytoImpl
    (fun n : I => pure (decide (n.val = 0)))
    (fun n : I => pure (decide (n.val > 0)))
    arrayOps.length arrayOps.length (vectorBounds arrayOps) (vectorBounds arrayOps)
    (fun length index => pure (JuliaLean.base.int.sub length index))
    (fun length index => pure (JuliaLean.base.int.sub length index))
    (fun difference count => pure (JuliaLean.base.int.add difference count))
    (fun difference count => pure (JuliaLean.base.int.add difference count))
    (fun count remaining => pure (JuliaLean.base.int.le count remaining))
    (fun count remaining => pure (JuliaLean.base.int.le count remaining))
    (fun _ _ => throw .bounds) (fun _ _ => throw .bounds)
    pure pure pure
    (fun data index => do
      let ref ← arrayOps.ref data
      arrayOps.shiftref ref (JuliaLean.base.int.sub index one))
    (fun data index => do
      let ref ← arrayOps.ref data
      arrayOps.shiftref ref (JuliaLean.base.int.sub index one))
    arrayOps.copyRef destination destinationIndex source sourceIndex count

def fillVectorRange {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Data Memory P : Type}
    (arrayOps : JuliaLean.base.array.Storage m Data Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (data : Data) (first count : I) (value : Byte) : m Data := do
  let indices := (List.range count.val.toNat).map fun index =>
    first + JInt.wrap .i64 (Int.ofNat index)
  let set := fun target byte index => do
    let _ ← setArrayByte arrayOps memoryOps (vectorBounds arrayOps) target byte index
    pure ()
  let fillTyped := JuliaLean.base.array.fillTyped (fun _ => pure indices) set
  JuliaLean.base.array.fillBang (fun _ : Byte => true) id (fun byte => pure byte)
    fillTyped data value

structure VectorMethods (m : Type → Type) (Ref Data NewData : Type) where
  lastIndex : Data → m I
  applicableResize : Data → I → m Bool
  resize : Data → I → m Unit
  similar : Ref → I → m NewData
  convertData : NewData → m Data
  copyIntoNew : NewData → I → Data → I → I → m Unit
  copyWithin : Data → I → Data → I → I → m Unit
  fillNew : NewData → Byte → m Unit
  fillView : Data → I → I → Byte → m Unit

def arrayVectorMethods {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Data Memory P : Type}
    (arrayOps : JuliaLean.base.array.Storage m Data Memory
      (JuliaLean.base.genericmemory.GenericMemoryRef Memory P))
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (allocateVector : I → m Data) :
    VectorMethods m (JuliaLean.base.genericmemory.GenericMemoryRef Memory P) Data Data where
  lastIndex := arrayOps.length
  applicableResize := fun _ _ => pure true
  resize := fun data length => do
    let _ ← JuliaLean.base.array.resize (fun value : I => pure value) arrayOps.length
      JuliaLean.base.int.and_int
      (JuliaLean.base.array.growbeg arrayOps (fun value : I => pure value)
        (JuliaLean.base.array.growbegInternal arrayOps))
      (JuliaLean.base.array.growend arrayOps (fun value : I => pure value)
        (JuliaLean.base.array.growendInternal arrayOps))
      (JuliaLean.base.array.deletebeg arrayOps (fun value : I => pure value))
      (JuliaLean.base.array.deleteend arrayOps (fun value : I => pure value))
      data length
    pure ()
  similar := fun data length => JuliaLean.base.array.similar418 allocateVector data length
  convertData := pure
  copyIntoNew := fun destination destinationIndex source sourceIndex count => do
    let _ ← copyVector arrayOps destination destinationIndex source sourceIndex count
    pure ()
  copyWithin := fun destination destinationIndex source sourceIndex count => do
    let _ ← copyVector arrayOps destination destinationIndex source sourceIndex count
    pure ()
  fillNew := fun data value => do
    let length ← arrayOps.length data
    let _ ← fillVectorRange arrayOps memoryOps data one length value
    pure ()
  fillView := fun data first last value => do
    let count := JuliaLean.base.int.add (JuliaLean.base.int.sub last first) one
    let _ ← fillVectorRange arrayOps memoryOps data first count value
    pure ()

def bindStorage {m : Type → Type} [Monad m] {Ref Data Mem NewData : Type}
    (arrayOps : JuliaLean.base.array.Storage m Data Mem Ref)
    (methods : VectorMethods m Ref Data NewData) :
    Storage m Ref Data NewData where
  Length := I
  LastIndex := I
  IndexDifference := I
  SpaceOther := Empty
  ShiftedLength := I
  AddedLength := I
  DesiredOther := Empty
  Bound := I
  length := arrayOps.length
  lastIndex := methods.lastIndex
  subtractIndex := fun last start => pure (JuliaLean.base.int.sub last start)
  minimumSpace := fun difference capacity => pure (.inl (JuliaLean.base.int.jmin difference capacity))
  spaceLess := fun space count => match space with
    | .inl value => pure (JuliaLean.base.int.lt value count)
    | .inr impossible => nomatch impossible
  shiftLength := fun length => pure (JuliaLean.base.int.lshr_int
    (JuliaLean.base.int.remT .u64 length) (JInt.wrap .u64 3) |> fun shifted => JInt.wrap .i64 shifted.val)
  reclaimEnough := fun reclaimable threshold => pure (JuliaLean.base.int.le threshold reclaimable)
  addLength := fun length count => pure (JuliaLean.base.int.add length count)
  subtractAvailable := fun total available => pure (.inl (JuliaLean.base.int.sub total available))
  desiredGreater := fun desired maxsize => match desired with
    | .inl value => pure (JuliaLean.base.int.lt maxsize value)
    | .inr impossible => nomatch impossible
  lengthLess := fun length maxsize => pure (JuliaLean.base.int.lt length maxsize)
  lengthToInt := pure
  minimumLength := fun length requested => pure (JuliaLean.base.int.jmin length requested)
  boundToInt := pure
  applicableResize := methods.applicableResize
  resize := methods.resize
  similar := methods.similar
  convertData := methods.convertData
  copyIntoNew := methods.copyIntoNew
  copyWithin := methods.copyWithin
  spanLength := fun first last => pure (rangeLength first last)
  fillNew := methods.fillNew
  fillView := methods.fillView

def copyStringMemory {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Memory P Pointer Token : Type}
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (copyOps : JuliaLean.base.genericmemory.MemoryCopyOps m Memory P I I I I Pointer Token)
    (destination : Memory) (destinationIndex : I) (source : Memory) (sourceIndex count : I) :
    m Unit := do
  let destinationRef ← memoryOps.memoryrefAt destination destinationIndex
  let sourceRef ← memoryOps.memoryrefAt source sourceIndex
  let _ ← JuliaLean.base.genericmemory.unsafeCopytoGenericRefs
    memoryOps memoryOps copyOps (fun byte => pure byte) (fun byte => pure byte)
    false copyOps.memoryrefoffset (isTrue rfl) destinationRef sourceRef count
  pure ()

def takeStringMemory {m : Type → Type} [Monad m] {Memory StringRef : Type}
    (memoryLength : Memory → I) (emptyString : m StringRef)
    (memoryToString : Memory → I → m StringRef) (memory : Memory) : m StringRef := do
  let count := memoryLength memory
  if JuliaLean.base.int.eq_int count zero then emptyString
  else memoryToString memory count

def takeStringIOBuffer {m : Type → Type} [Monad m]
    [MonadExceptOf IOErr m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    {Ref Memory P Pointer Token StringRef : Type}
    (access : Access m Ref Memory)
    (memoryOps : JuliaLean.base.genericmemory.MemoryAccessOps m Memory P Byte Byte)
    (memoryLength : Memory → I)
    (copyOps : JuliaLean.base.genericmemory.MemoryCopyOps m Memory P I I I I Pointer Token)
    (emptyString : m StringRef) (memoryToString : Memory → I → m StringRef)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m Memory)
    (ref : Ref) : m StringRef :=
  source_takestring_IOBuffer access
    (fun first last => pure (rangeLength first last))
    (fun first last => pure (JuliaLean.base.int.lt last first))
    emptyString memoryToString
    (fun count : U => source_StringMemory (fun size : U => pure size)
      allocateString stringToMemory count)
    (fun count : I => source_StringMemory
      (fun size : I => liftNative (JuliaLean.base.int.convert .u64 size))
      allocateString stringToMemory count)
    (copyStringMemory memoryOps copyOps)
    (takeStringMemory memoryLength emptyString memoryToString) ref

inductive DenseByteVector where
  | array (handle : Nat) (baseAddress : JuliaLean.base.pointer.U64)
  | memory (handle : Nat) (baseAddress : JuliaLean.base.pointer.U64)
  deriving DecidableEq

abbrev ArrayWorld (Ref Data : Type) :=
  BufferHeap Ref Data (JuliaLean.base.array.MutableMemory Byte)

def liftArrayMutationIO {World A : Type}
    (getMem : World → JuliaLean.base.array.MutableMemory Byte)
    (setMem : World → JuliaLean.base.array.MutableMemory Byte → World)
    (action : JuliaLean.base.array.MutationM Byte A) : JuliaLean.base.io.M World A :=
  fun world =>
    let (result, mem) := action.run (getMem world)
    let world' := setMem world mem
    match result with
    | .ok value => some (.ok (value, world'))
    | .error error => some (.error (arrayIOError error, world'))

def memoryByteInBoundsWith {m : Type → Type} [Monad m]
    (liftMut : {A : Type} → JuliaLean.base.array.MutationM Byte A → m A)
    (memory : Nat) (index : I) : m Bool := do
  let contents ← liftMut (JuliaLean.base.array.memoryRead memory)
  pure (decide (1 ≤ index.val ∧ index.val ≤ (contents.length : Int)))

def readMemoryByteWith {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    (liftMut : {A : Type} → JuliaLean.base.array.MutationM Byte A → m A)
    (memory : Nat) (index : I) : m Byte := do
  let contents ← liftMut (JuliaLean.base.array.memoryRead memory)
  if !(1 ≤ index.val) then
    throwThe JuliaLean.base.array.Error .bounds
  match contents[(index.val - 1).toNat]? with
  | some (some value) => pure value
  | some none => throwThe JuliaLean.base.array.Error .undefinedReference
  | none => throwThe JuliaLean.base.array.Error .bounds

def mutableByteMemoryOpsWith {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m]
    (liftMut : {A : Type} → JuliaLean.base.array.MutationM Byte A → m A) :
    JuliaLean.base.genericmemory.MemoryAccessOps m Nat I Byte Byte where
  memoryref memory := pure ⟨memory, zero⟩
  memoryrefAt memory index := pure ⟨memory, index - one⟩
  memoryrefNew reference index _ :=
    pure ⟨reference.mem, reference.ptr_or_offset + index - one⟩
  memoryrefIsAssigned reference _ _ := do
    let contents ← liftMut (JuliaLean.base.array.memoryRead reference.mem)
    pure ((contents[(reference.ptr_or_offset.val).toNat]?.join).isSome)
  memoryrefUnset reference _ _ :=
    liftMut (JuliaLean.base.array.memoryWrite reference.mem
      (reference.ptr_or_offset + one) none)
  memoryrefSet reference value _ _ :=
    liftMut (JuliaLean.base.array.memoryWrite reference.mem
      (reference.ptr_or_offset + one) (some value))
  defaultOrderMemory _ := .notAtomic
  defaultOrderRef _ := .notAtomic
  checkboundsBool memory index := memoryByteInBoundsWith liftMut memory index
  checkbounds memory index := do
    if !(← memoryByteInBoundsWith liftMut memory index) then
      throwThe JuliaLean.base.array.Error .bounds
  castElement value := some value
  convertElement value := pure value
  getindex memory index := readMemoryByteWith liftMut memory index

def denseBytePointer : DenseByteVector → JuliaLean.base.pointer.Ptr Byte
  | .array _ address | .memory _ address => ⟨address⟩

def pointerAtDenseByte (data : DenseByteVector) (index : I) :
    JuliaLean.base.pointer.Ptr Byte :=
  JuliaLean.base.pointer.ptrAddI64 (denseBytePointer data) (index - one)

/-!
## Single-`ByteHeap` `Memory{UInt8}` representation (`ByteMemory`)
`Fields ByteMemory` stores immutable `Memory{UInt8}` header metadata (`id`, `address`, `length`),
while all element reads, writes, copies, fills, and C pointer operations act on the one shared
`ByteHeap`. C string/memory entry points (`_string_n`, `unsafe_wrap`, `jl_genericmemory_to_string`)
are named typed primitive parameters per rule 18a.
-/

structure ByteMemory where
  id : Nat
  address : JuliaLean.base.pointer.U64
  length : I
  deriving DecidableEq

def byteMemoryLength (d : ByteMemory) : I := d.length

def byteMemoryPointer (d : ByteMemory) (index : I) : JuliaLean.base.pointer.Ptr Byte :=
  JuliaLean.base.pointer.ptrAddI64 ⟨d.address⟩ (JuliaLean.base.int.sub index one)

def byteMemoryCheckBounds {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    (d : ByteMemory) (index : I) : m Unit := do
  if !(JuliaLean.base.abstractarray.checkindexOneTo d.length index) then
    throw (.jl .boundsError)

def byteMemoryGetindex {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    (heap : HeapAccess m) (d : ByteMemory) (index : I) : m Byte := do
  byteMemoryCheckBounds d index
  let bytes ← heap.get
  let addr := (byteMemoryPointer d index).address.val.toNat
  pure (bytes.readByte addr)

def byteMemoryAccessOps {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    (heap : HeapAccess m) :
    JuliaLean.base.genericmemory.MemoryAccessOps m ByteMemory I Byte Byte where
  memoryref d := pure ⟨d, zero⟩
  memoryrefAt d index := do
    byteMemoryCheckBounds d index
    pure ⟨d, JuliaLean.base.int.sub index one⟩
  memoryrefNew ref index boundsChecking := do
    let target := JuliaLean.base.int.add ref.ptr_or_offset index
    if boundsChecking then byteMemoryCheckBounds ref.mem target
    pure ⟨ref.mem, JuliaLean.base.int.sub target one⟩
  memoryrefIsAssigned _ _ _ := pure true
  memoryrefUnset _ _ _ := pure ()
  memoryrefSet ref value _ boundsChecking := do
    let idx := JuliaLean.base.int.add ref.ptr_or_offset one
    if boundsChecking then byteMemoryCheckBounds ref.mem idx
    let bytes ← heap.get
    let addr := (byteMemoryPointer ref.mem idx).address.val.toNat
    heap.set (bytes.writeByte addr value)
  defaultOrderMemory _ := .notAtomic
  defaultOrderRef _ := .notAtomic
  checkboundsBool d index := pure (JuliaLean.base.abstractarray.checkindexOneTo d.length index)
  checkbounds d index := byteMemoryCheckBounds d index
  castElement value := some value
  convertElement value := pure value
  getindex d index := byteMemoryGetindex heap d index

def byteMemorySetindex {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    (heap : HeapAccess m) (d : ByteMemory) (index : I) (value : Byte) : m Unit := do
  let _ ← JuliaLean.base.genericmemory.setindexMemoryRaw
    (byteMemoryAccessOps heap) true d value index
  pure ()

def byteMemoryCopyOps {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    (heap : HeapAccess m) :
    JuliaLean.base.genericmemory.MemoryCopyOps m ByteMemory I I I I I
      (JuliaLean.base.pointer.Ptr Byte) Unit where
  isZero n := JuliaLean.base.int.eq_int n zero
  toInt n := pure n
  byteCount _ n := pure n
  checkEnd ref n :=
    (byteMemoryAccessOps heap).memoryrefNew ref n true
  memoryrefDest d doffs :=
    (byteMemoryAccessOps heap).memoryrefAt d doffs
  memoryrefSource s soffs :=
    (byteMemoryAccessOps heap).memoryrefAt s soffs
  memoryrefoffset ref := JuliaLean.base.int.add ref.ptr_or_offset one
  isBitsType _ := true
  gcPreserveBegin _ := ()
  gcPreserveEnd _ := pure ()
  unsafeConvert ref :=
    pure (byteMemoryPointer ref.mem (JuliaLean.base.int.add ref.ptr_or_offset one))
  memmove pdest psrc n := do
    let bytes ← heap.get
    let slice := bytes.readBytes psrc.address.val.toNat n.val.toNat
    heap.set (bytes.writeBytes pdest.address.val.toNat slice)
  ccallCopy dst dstOff src srcOff n := do
    let bytes ← heap.get
    let psrc := byteMemoryPointer src (JuliaLean.base.int.add srcOff one)
    let pdest := byteMemoryPointer dst (JuliaLean.base.int.add dstOff one)
    let slice := bytes.readBytes psrc.address.val.toNat n.val.toNat
    heap.set (bytes.writeBytes pdest.address.val.toNat slice)
  pointerDest d doffs := pure (byteMemoryPointer d doffs)
  pointerSource s soffs := pure (byteMemoryPointer s soffs)
  pointerLess p1 p2 := JuliaLean.base.int.lt p1.address p2.address
  pointerGreater p1 p2 := JuliaLean.base.int.lt p2.address p1.address
  sourceEnd soffs n := pure (JuliaLean.base.int.sub (JuliaLean.base.int.add soffs n) one)
  forwardRange n :=
    pure ((List.range n.val.toNat).map fun k => JuliaLean.base.int.lit .i64 (Int.ofNat (k + 1)))
  backwardRange n :=
    pure (((List.range n.val.toNat).map fun k => JuliaLean.base.int.lit .i64 (Int.ofNat (k + 1))).reverse)
  destIndex doffs k :=
    pure (JuliaLean.base.int.sub (JuliaLean.base.int.add doffs k) one)
  sourceIndex soffs k :=
    pure (JuliaLean.base.int.sub (JuliaLean.base.int.add soffs k) one)

def byteMemoryCopyto {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    (heap : HeapAccess m) (dest : ByteMemory) (doffs : I)
    (src : ByteMemory) (soffs count : I) : m Unit := do
  let _ : MonadExceptOf JuliaLean.base.array.Error m := {
    throw := fun
      | .bounds => throwThe IOErr (.jl .boundsError)
      | .argument msg => throwThe IOErr (.jl (.argumentError msg))
      | .inexact => throwThe IOErr (.jl (.inexactError "convert"))
      | .overflow => throwThe IOErr (.jl (.overflowError ""))
      | .divide => throwThe IOErr (.jl .divideError)
      | .typeError _ => throwThe IOErr .typeError
      | .dimensionMismatch msg => throwThe IOErr (.jl (.argumentError msg))
      | .method name => throwThe IOErr (.jl (.methodError name))
      | .assertion msg => throwThe IOErr (.errorException msg)
      | .concurrency msg => throwThe IOErr (.errorException msg)
      | .thrownNothing => throwThe IOErr (.errorException "Nothing")
      | .undefinedReference => throwThe IOErr (.errorException "UndefRefError")
      | .showError err => throwThe IOErr (.showError err)
    tryCatch := fun body _ => body
  }
  let memOps := byteMemoryAccessOps heap
  let copyOps := byteMemoryCopyOps heap
  let _ ← JuliaLean.base.genericmemory.copytoMemoryOffsets
    (JuliaLean.base.array.copytoImpl
      (fun n : I => pure (JuliaLean.base.int.eq_int n zero))
      (fun n : I => pure (JuliaLean.base.int.lt zero n))
      (fun d : ByteMemory => pure d.length)
      (fun d : ByteMemory => pure d.length)
      memOps.checkbounds memOps.checkbounds
      (fun len idx => pure (JuliaLean.base.int.sub len idx))
      (fun len idx => pure (JuliaLean.base.int.sub len idx))
      (fun diff n => pure (JuliaLean.base.int.add diff n))
      (fun diff n => pure (JuliaLean.base.int.add diff n))
      (fun n rem => pure (JuliaLean.base.int.le n rem))
      (fun n rem => pure (JuliaLean.base.int.le n rem))
      (fun _ _ => throwThe IOErr (.jl .boundsError))
      (fun _ n => throwThe IOErr (.jl (.argumentError
        ("tried to copy n=" ++ toString n.val ++ " elements, but n should be nonnegative"))))
      pure pure pure
      memOps.memoryrefAt memOps.memoryrefAt
      (fun dstRef srcRef n => do
        let _ ← JuliaLean.base.genericmemory.unsafeCopytoGenericRefs
          memOps memOps copyOps pure pure false copyOps.memoryrefoffset (isTrue rfl)
          dstRef srcRef n
        pure ()))
    dest doffs src soffs count
  pure ()

def byteMemoryFillNew {m : Type → Type} [Monad m]
    (heap : HeapAccess m) (d : ByteMemory) (value : Byte) : m Unit := do
  let _ ← JuliaLean.base.genericmemory.fillByteMemory
    (fun _ => Byte) (fun _ => True) (fun _ b => some b) (fun _ b => pure b)
    (fun _ => ()) (fun _ => pure ())
    (fun mem => pure (⟨mem.address⟩ : JuliaLean.base.pointer.Ptr Byte))
    (fun ptr byte count => do
      let bytes ← heap.get
      heap.set (bytes.writeBytes ptr.address.val.toNat (List.replicate count.val.toNat byte)))
    (fun mem => pure (JuliaLean.base.int.remT .u64 mem.length))
    d value True.intro
  pure ()

def byteMemoryFill {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    (heap : HeapAccess m) (d : ByteMemory) (first last : I) (value : Byte) : m Unit := do
  let ok ← match JuliaLean.base.abstractarray.checkindexRange
      (fun (a, b) => pure (JuliaLean.base.int.lt b a))
      (fun (a, _) => pure a) (fun (_, b) => pure b)
      (fun len idx => pure (JuliaLean.base.abstractarray.checkindexOneTo len idx))
      d.length (first, last) with
    | .ok valid => pure valid
    | .error _ => throw (.jl .boundsError)
  if !ok then throw (.jl .boundsError)
  let count := rangeLength first last
  let indices := (List.range count.val.toNat).map fun offset =>
    JuliaLean.base.int.add first (JuliaLean.base.int.lit .i64 (Int.ofNat offset))
  let fillTyped := JuliaLean.base.array.fillTyped (fun _ => pure indices)
    (fun target byte index => byteMemorySetindex heap target index byte)
  let _ ← JuliaLean.base.array.fillBang (fun _ : Byte => true) id pure fillTyped d value
  pure ()

def byteMemoryStorage {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {Ref StringRef : Type}
    (access : Access m Ref ByteMemory) (heap : HeapAccess m)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m ByteMemory) :
    Storage m Ref ByteMemory ByteMemory where
  Length := I
  LastIndex := I
  IndexDifference := I
  SpaceOther := Empty
  ShiftedLength := I
  AddedLength := I
  DesiredOther := Empty
  Bound := I
  length := fun d => pure d.length
  lastIndex := fun d => pure d.length
  subtractIndex := fun last start => pure (JuliaLean.base.int.sub last start)
  minimumSpace := fun difference capacity => pure (.inl (JuliaLean.base.int.jmin difference capacity))
  spaceLess := fun space count => match space with
    | .inl value => pure (JuliaLean.base.int.lt value count)
    | .inr impossible => nomatch impossible
  shiftLength := fun length => pure (JuliaLean.base.int.lshr_int
    (JuliaLean.base.int.remT .u64 length) (JInt.wrap .u64 3) |> fun shifted => JInt.wrap .i64 shifted.val)
  reclaimEnough := fun reclaimable threshold => pure (JuliaLean.base.int.le threshold reclaimable)
  addLength := fun length count => pure (JuliaLean.base.int.add length count)
  subtractAvailable := fun total available => pure (.inl (JuliaLean.base.int.sub total available))
  desiredGreater := fun desired maxsize => match desired with
    | .inl value => pure (JuliaLean.base.int.lt maxsize value)
    | .inr impossible => nomatch impossible
  lengthLess := fun length maxsize => pure (JuliaLean.base.int.lt length maxsize)
  lengthToInt := pure
  minimumLength := fun length requested => pure (JuliaLean.base.int.jmin length requested)
  boundToInt := pure
  applicableResize := fun _ _ => pure false
  resize := fun _ _ => throw (.jl (.methodError "resize!"))
  similar := fun ref size =>
    source_similar_data_IOBuffer access allocateString stringToMemory ref size
  convertData := pure
  copyIntoNew := fun dest doffs src soffs count =>
    byteMemoryCopyto heap dest doffs src soffs count
  copyWithin := fun dest doffs src soffs count =>
    byteMemoryCopyto heap dest doffs src soffs count
  spanLength := fun first last => pure (rangeLength first last)
  fillNew := fun d value =>
    byteMemoryFillNew heap d value
  fillView := fun d first last value =>
    byteMemoryFill heap d first last value
def byteMemoryEnsureRoom {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {Ref StringRef : Type}
    (access : Access m Ref ByteMemory) (heap : HeapAccess m)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m ByteMemory)
    (ref : Ref) (count : U) : m Ref :=
  source_ensureroom access (byteMemoryStorage access heap allocateString stringToMemory) ref count

def byteMemoryEnsureRoomInt {m : Type → Type} [Monad m] [MonadExceptOf IOErr m] {Ref StringRef : Type}
    (access : Access m Ref ByteMemory) (heap : HeapAccess m)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m ByteMemory)
    (ref : Ref) (count : I) : m Ref :=
  source_ensureroom_int access (byteMemoryStorage access heap allocateString stringToMemory) ref count

def byteMemoryEmptyIOBuffer {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {N Hint StringRef Ref : Type} (access : Access m Ref ByteMemory)
    (maximum : IntegerConversions N) (hintConversion : IntegerConversions Hint)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m ByteMemory)
    (read write append truncate : Option Bool) (maxsize : N) (hint : Option Hint) : m Ref :=
  iobufferEmpty access maximum hintConversion allocateString stringToMemory
    (fun d => pure d.length) pure read write append truncate maxsize hint

def byteMemoryTakeString {m : Type → Type} [Monad m] [MonadExceptOf IOErr m]
    {Ref StringRef : Type} (access : Access m Ref ByteMemory) (heap : HeapAccess m)
    (emptyString : m StringRef) (memoryToString : ByteMemory → I → m StringRef)
    (allocateString : U → m StringRef) (stringToMemory : StringRef → m ByteMemory)
    (ref : Ref) : m StringRef :=
  source_takestring_IOBuffer access
    (fun first last => pure (rangeLength first last))
    (fun first last => pure (JuliaLean.base.int.lt last first))
    emptyString memoryToString
    (fun count : U => source_StringMemory pure allocateString stringToMemory count)
    (fun count : I => source_StringMemory
      (fun sz : I => liftNative (JuliaLean.base.int.convert .u64 sz))
      allocateString stringToMemory count)
    (byteMemoryCopyto heap)
    (takeStringMemory (fun d => d.length) emptyString memoryToString) ref

end JuliaLean.base.iobuffer

namespace JuliaLean.base.iobuffer.SharedMemory

open JuliaLean

abbrev Heap (Other : Type) := BufferHeap Nat ByteMemory Other
abbrev Action (Other A : Type) := EStateM IOErr (Heap Other) A

def access {Other : Type} (allocateObject : Fields ByteMemory → Action Other Nat) :
    Access (Action Other) Nat ByteMemory :=
  bindHeapAccess get set (fun message => throwThe IOErr (.errorException message))
    { sameRef := fun a b => decide (a = b), allocateObject }

def pointerHeap {Other : Type} : HeapAccess (Action Other) :=
  bindHeapPointerHeap get set

instance {Other : Type} : MonadExceptOf JuliaLean.base.pointer.PointerError (Action Other) where
  throw
    | .julia error => throwThe IOErr (.jl error)
    | .errorException message => throwThe IOErr (.errorException message)
    | .methodError name => throwThe IOErr (.jl (.methodError name))
  tryCatch body handler := fun heap =>
    match body heap with
    | .ok value after => .ok value after
    | .error (.jl error) after => handler (.julia error) after
    | .error (.errorException message) after => handler (.errorException message) after
    | .error error after => .error error after

/-- Memory-backed peek uses the installed dense pointer load and the same byte
heap as writes. GC-root bookkeeping is erased; it does not change buffer fields.
The codec specifies the platform representation and has no mutable operations.
Source: base/iobuffer.jl:418-430; base/subarray.jl:365-370
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def peek {Other : Type} (allocateObject : Fields ByteMemory → Action Other Nat)
    (codec : (kind : Multibyte) → JuliaLean.base.pointer.ByteCodec (valueType kind))
    (ref : Nat) (kind : Multibyte) : Action Other (valueType kind) :=
  source_peek_multibyte_dense (access allocateObject) pointerHeap codec
    (fun memory index => pure (byteMemoryPointer memory index))
    (fun _ _ body => body ()) ref kind

/-- The fixed Memory storage dispatch selects dense peek before incrementing
the native pointer. Reads and aliased writes share the same ByteHeap.
Source: base/iobuffer.jl:432-436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
def read {Other : Type} (allocateObject : Fields ByteMemory → Action Other Nat)
    (codec : (kind : Multibyte) → JuliaLean.base.pointer.ByteCodec (valueType kind))
    (ref : Nat) (kind : Multibyte) : Action Other (valueType kind) :=
  readMultibyteDense (access allocateObject) pointerHeap codec
    (fun memory index => pure (byteMemoryPointer memory index))
    (fun _ _ body => body ()) ref kind

end JuliaLean.base.iobuffer.SharedMemory

/-!
Model of `GenericIOBuffer` (`base/iobuffer.jl`, master `bbfa0ce4150`) and the
generic `mark`/`reset`/`peek` methods of `base/io.jl` it relies on.

* `data` is the backing vector as a list of bytes; Julia index `k` is list
  index `k - 1`. Freshly allocated memory (`StringMemory`) is uninitialised in
  Julia; its bytes are zero here and are never observable.
* `isMem` is `T === Memory{UInt8}` (an `IOBuffer`); otherwise the buffer is a
  `GenericIOBuffer` over another vector type such as a `SubArray`, whose
  `similar` is not a `T` and which has no `resize!`.
* The `Int` fields are `JInt64` and use Julia's wrapping arithmetic.
* A mutation made before an exception persists (`EStateM`).
* `IOErr.outOfBounds` marks an `@inbounds`/pointer access outside `data`,
  which Julia does not check (undefined behaviour).
-/

namespace JuliaLean.IOBuffers

open JuliaLean

/-- Julia `Int`. -/
abbrev I := JInt64
/-- Julia `UInt`. -/
abbrev U := JInt .u64

/-- `x % Int`. -/
def i (x : Int) : I := JInt.wrap .i64 x
/-- `x % UInt`. -/
def u (x : Int) : U := JInt.wrap .u64 x

/-- `typemax(Int)`. -/
def imaxval : I := i (2 ^ 63 - 1)

/-- `max(a, b)` on `Int`. -/
def imax (a b : I) : I := if b.val < a.val then a else b
/-- `min(a, b)` on `Int`. -/
def imin (a b : I) : I := if b.val < a.val then b else a
/-- `min(a, b)` on `UInt`. -/
def uminU (a b : U) : U := if b.val < a.val then b else a
/-- `clamp(x, lo, hi)` on `Int` (`base/intfuncs.jl`): `hi` is tested first. -/
def clampI (x lo hi : I) : I := if x.val > hi.val then hi else if x.val < lo.val then lo else x
/-- `clamp(x, Int)` of a wider integer `x`. -/
def clampToI (x : Int) : I :=
  if x > 2 ^ 63 - 1 then imaxval else if x < -2 ^ 63 then i (-2 ^ 63) else i x

/-- Exceptions thrown by the modelled methods. -/
inductive IOErr where
  | jl (e : JlError)
  | eofError
  | errorException (msg : String)
  | typeError
  /-- An unchecked access outside `data` (undefined behaviour in Julia). -/
  | outOfBounds
  deriving Repr, DecidableEq, Inhabited

/-- Name of the Julia exception type. -/
def IOErr.name : IOErr → String
  | .jl (.overflowError _) => "OverflowError"
  | .jl (.argumentError _) => "ArgumentError"
  | .jl .boundsError => "BoundsError"
  | .jl (.inexactError _) => "InexactError"
  | .jl .divideError => "DivideError"
  | .jl (.domainError _) => "DomainError"
  | .jl (.methodError _) => "MethodError"
  | .jl .eofError => "EOFError"
  | .eofError => "EOFError"
  | .errorException _ => "ErrorException"
  | .typeError => "TypeError"
  | .outOfBounds => "UB"

/-- The fields of `GenericIOBuffer`, `base/iobuffer.jl:33-93`. `oc` is
`offset_or_compacted`. -/
structure IOBuf where
  data : List UInt8
  isMem : Bool
  reinit : Bool
  readable : Bool
  writable : Bool
  seekable : Bool
  append : Bool
  size : I
  maxsize : I
  ptr : I
  oc : I
  mark : I
  deriving DecidableEq

/-- Mutating methods on an `IOBuffer`. -/
abbrev M := EStateM IOErr IOBuf

def lift {α} : Except IOErr α → M α
  | .ok a => pure a
  | .error e => throw e

def throwArg {α} (msg : String) : M α := throw (.jl (.argumentError msg))

/-- `convert(Int, x)` / `Int(x)`. -/
def toI (x : Int) : Except IOErr I :=
  match JInt.convert (IntTy.i64.name) .i64 x with
  | .ok v => .ok v
  | .error e => .error (.jl e)

/-- `convert(UInt, x)`. -/
def toU (x : Int) : Except IOErr U :=
  match JInt.convert (IntTy.u64.name) .u64 x with
  | .ok v => .ok v
  | .error e => .error (.jl e)

/-! ## Memory primitives -/

/-- `data[a:b]` (1-based, inclusive) when `1 ≤ a` and `b ≤ length(data)`. -/
def slice (d : List UInt8) (a b : Int) : List UInt8 :=
  (d.drop (a - 1).toNat).take (b - a + 1).toNat

/-- Checked `data[k]`. -/
def getChecked (d : List UInt8) (k : I) : Except IOErr UInt8 :=
  if 1 ≤ k.val ∧ k.val ≤ d.length then .ok (d.getD (k.val - 1).toNat 0) else .error (.jl .boundsError)

/-- Checked `data[k] = b`. -/
def setChecked (d : List UInt8) (k : I) (b : UInt8) : Except IOErr (List UInt8) :=
  if 1 ≤ k.val ∧ k.val ≤ d.length then .ok (d.set (k.val - 1).toNat b) else .error (.jl .boundsError)

/-- `copyto!(dest, doffs, src, soffs, n)` (`base/genericmemory.jl:266`, `base/array.jl`):
`n == 0` returns, a negative `n` is an `ArgumentError`, out-of-range ranges a `BoundsError`. -/
def copyto (dest : List UInt8) (doffs : I) (src : List UInt8) (soffs n : I) : Except IOErr (List UInt8) :=
  if n.val = 0 then .ok dest
  else if n.val < 0 then .error (.jl (.argumentError "tried to copy n=" ))
  else if 1 ≤ doffs.val ∧ doffs.val + n.val - 1 ≤ dest.length ∧ 1 ≤ soffs.val ∧ soffs.val + n.val - 1 ≤ src.length then
    .ok (dest.take (doffs.val - 1).toNat ++ slice src soffs.val (soffs.val + n.val - 1) ++
      dest.drop (doffs.val - 1 + n.val).toNat)
  else .error (.jl .boundsError)

/-- Write `bs` at index `k` onwards: `_unsafe_write`, `base/iobuffer.jl:923-946`. Memory
data is written through a pointer (unchecked); other vectors use checked `setindex!`. -/
def writeAt (isMem : Bool) (d : List UInt8) (k : I) (bs : List UInt8) : Except IOErr (List UInt8) :=
  if bs.length = 0 then .ok d
  else if 1 ≤ k.val ∧ k.val + bs.length - 1 ≤ d.length then
    .ok (d.take (k.val - 1).toNat ++ bs ++ d.drop (k.val - 1 + bs.length).toNat)
  else if isMem then .error .outOfBounds else .error (.jl .boundsError)

/-- Read `n` bytes from index `k` (pointer copy, `unsafe_read!`, `base/iobuffer.jl:361-378`). -/
def readAt (d : List UInt8) (k : I) (n : Nat) : Except IOErr (List UInt8) :=
  if n = 0 then .ok []
  else if 1 ≤ k.val ∧ k.val + n - 1 ≤ d.length then .ok (slice d k.val (k.val + n - 1))
  else .error .outOfBounds

/-- `fill!(view(data, a:b), 0x00)`. -/
def fillZero (d : List UInt8) (a b : I) : Except IOErr (List UInt8) :=
  if b.val < a.val then .ok d
  else if 1 ≤ a.val ∧ b.val ≤ d.length then
    .ok (d.take (a.val - 1).toNat ++ List.replicate (b.val - a.val + 1).toNat 0 ++ d.drop b.val.toNat)
  else .error (.jl .boundsError)

/-- `length(a:b)` for a `UnitRange{Int}`. -/
def rangeLength (a b : I) : I := if b.val < a.val then i 0 else b - a + i 1

/-- `StringMemory(n)`, `base/iobuffer.jl:167`: `_string_n` converts `n` to `Csize_t`. -/
def stringMemory (n : I) : Except IOErr (List UInt8) :=
  if n.val < 0 then .error (.jl (.inexactError "convert")) else .ok (List.replicate n.val.toNat 0)

/-- Number of significant bits of `n`, i.e. `64 - ctlz_int(n)` for `0 ≤ n < 2^64`. -/
def bitLength : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitLength fuel (n / 2) + 1

/-- `overallocation(maxsize)`, `base/array.jl:1102-1112`; a negative argument has no
leading zeros. -/
def overallocation (n : I) : I :=
  let exp2 : Nat := if n.val < 0 then 64 else bitLength 64 n.val.toNat
  let extra := i (2 ^ (exp2 * 7 / 8)) * i 3 + i (n.val.tdiv 8)
  if n.val > (imaxval - extra).val then imaxval else n + extra

/-! ## Field accessors, `base/iobuffer.jl` -/

/-- `get_offset`, `base/iobuffer.jl:163`. -/
def getOffset (io : IOBuf) : I := imax (i 0) io.oc
/-- `get_compacted`, `base/iobuffer.jl:164`. -/
def getCompacted (io : IOBuf) : I := imax (i 0) (-io.oc)
/-- `bytesavailable`, `base/iobuffer.jl:467`. -/
def bytesavailable (io : IOBuf) : I := io.size - io.ptr + i 1
/-- `position`, `base/iobuffer.jl:470-473`. -/
def position (io : IOBuf) : I := io.ptr - io.oc - i 1
/-- `filesize`, `base/iobuffer.jl:464`. -/
def filesize (io : IOBuf) : I := if io.seekable then io.size - getOffset io else bytesavailable io
/-- `eof`, `base/iobuffer.jl:691`. -/
def eof (io : IOBuf) : Bool := decide ((io.ptr - i 1).val ≥ io.size.val)
/-- `ismarked`, `base/io.jl:1615`. -/
def ismarked (io : IOBuf) : Bool := decide (io.mark.val ≥ 0)

/-- `translate_seek_position`, `base/iobuffer.jl:500-510`. -/
def translateSeekPosition (io : IOBuf) (n : I) : I := clampToI (n.val + io.oc.val + 1)

/-- `get_used_span`, `base/iobuffer.jl:662-673`; defined only for `IOBuffer`. -/
def getUsedSpan (io : IOBuf) : Except IOErr (I × I) :=
  if !io.isMem then .error (.jl (.methodError "get_used_span"))
  else if io.seekable then .ok (getOffset io + i 1, io.size)
  else if io.mark.val > -1 then .ok (imin io.ptr (translateSeekPosition io io.mark), io.size)
  else .ok (io.ptr, io.size)

/-- `_similar_data`, `base/iobuffer.jl:296-297`: `StringMemory` for an `IOBuffer`; for other
vector types `similar` returns a `Vector`, which cannot be stored in the `data::T` field. -/
def similarData (io : IOBuf) (n : I) : Except IOErr (List UInt8) :=
  if io.isMem then stringMemory n else .error (.jl (.methodError "convert"))

/-! ## Constructors -/

/-- A `Vector{UInt8}`: its memory, `memoryrefoffset(ref) - 1`, and its length. -/
structure Vec where
  mem : List UInt8
  off : Nat
  len : Nat
  deriving DecidableEq

/-- The `data` argument of the constructors. -/
inductive DataArg where
  | vec (v : Vec)
  | mem (m : List UInt8)
  /-- A non-`Memory` `AbstractVector{UInt8}` with one-based indexing (e.g. a `view`). -/
  | other (d : List UInt8)
  deriving DecidableEq

/-- `open_flags` result. -/
structure Flags where
  read : Bool
  write : Bool
  create : Bool
  truncate : Bool
  append : Bool

/-- `open_flags`, `base/io.jl:401-427`. -/
def openFlags (read write create truncate append : Option Bool) : Flags :=
  let (create, truncate) :=
    if write = some true ∧ read ≠ some true ∧ append ≠ some true then
      (if create.isNone then some true else create, if truncate.isNone then some true else truncate)
    else (create, truncate)
  let (write, create) :=
    if truncate = some true ∨ append = some true then
      (if write.isNone then some true else write, if create.isNone then some true else create)
    else (write, create)
  let write := write.getD false
  { read := read.getD (!write), write, create := create.getD false,
    truncate := truncate.getD false, append := append.getD false }

/-- `_new_generic_iobuffer`, `base/iobuffer.jl:96-107`. -/
def newBuf (data : List UInt8) (isMem readable writable seekable append : Bool) (maxsize : I) : IOBuf :=
  { data, isMem, reinit := false, readable, writable, seekable, append, size := i data.length,
    maxsize, ptr := i 1, oc := i 0, mark := i (-1) }

/-- `GenericIOBuffer(data, readable, writable, seekable, append, maxsize, truncate)`:
`base/iobuffer.jl:110-130` for `Memory`/other vectors, `141-161` for a `Vector`. -/
def genericIOBuffer (data : DataArg) (readable writable seekable append : Bool) (maxsize : Int)
    (truncate : Bool) : Except IOErr IOBuf := do
  match data with
  | .vec v =>
    let mz ← toI maxsize
    if !truncate ∧ mz.val < v.len then .error (.jl (.argumentError "maxsize must not be smaller than data length"))
    let buf := newBuf v.mem true readable writable seekable append mz
    let buf := { buf with oc := i v.off, ptr := i (v.off + 1) }
    pure { buf with size := if truncate then i v.off else i (v.len + v.off) }
  | .mem d | .other d =>
    let mz ← toI maxsize
    if !truncate ∧ mz.val < d.length then .error (.jl (.argumentError "maxsize must not be smaller than data length"))
    let buf := newBuf d (match data with | .mem _ => true | _ => false) readable writable seekable append mz
    pure (if truncate then { buf with size := buf.oc } else buf)

/-- `IOBuffer(data; read, write, append, truncate, maxsize)`, `base/iobuffer.jl:230-244`
(no `sizehint`). -/
def iobufferData (data : DataArg) (read write append truncate : Option Bool) (maxsize : Int := 2 ^ 63 - 1) :
    Except IOErr IOBuf :=
  let f := openFlags read write none truncate append
  genericIOBuffer data f.read f.write true f.append maxsize f.truncate

/-- `IOBuffer(; read=true, write=true, append, truncate=true, maxsize, sizehint)`,
`base/iobuffer.jl:246-270`. -/
def iobufferEmpty (read write append truncate : Option Bool) (maxsize : Int := 2 ^ 63 - 1)
    (sizehint : Option Int := none) : Except IOErr IOBuf := do
  let mz ← toI maxsize
  if mz.val < 0 then .error (.jl (.argumentError "negative maxsize"))
  let size ← match sizehint with
    | some s => do let s ← toI s; pure (imin mz (imax (i 0) s))
    | none => pure (imin mz (i 32))
  let f := openFlags read write none truncate append
  let d ← stringMemory size
  pure { newBuf d true f.read f.write true f.append mz with size := i 0 }

/-- `IOBuffer()`. -/
def iobuffer : Except IOErr IOBuf := iobufferEmpty (some true) (some true) none (some true)

/-- `IOBuffer(str::String)`, `base/strings/io.jl:306`. -/
def iobufferString (s : List UInt8) : Except IOErr IOBuf :=
  iobufferData (.vec ⟨s, 0, s.length⟩) none none none none

/-- `PipeBuffer(data=Memory{UInt8}(); maxsize::Int=typemax(Int))`, `base/iobuffer.jl:284-285`.
The keyword is declared `::Int`, so another integer type `t` is a `TypeError`. -/
def pipeBuffer (data : DataArg := .mem []) (t : IntTy := .i64) (maxsize : Int := 2 ^ 63 - 1) :
    Except IOErr IOBuf :=
  if t ≠ .i64 then .error .typeError
  else genericIOBuffer data true true false true maxsize false

/-- `PipeBuffer(maxsize::Integer)`, `base/iobuffer.jl:286`. -/
def pipeBufferN (t : IntTy) (maxsize : Int) : Except IOErr IOBuf := do
  let d ← if maxsize < 0 then Except.error (IOErr.jl (.inexactError "convert"))
    else pure (List.replicate maxsize.toNat 0)
  let x ← pipeBuffer (.mem d) t maxsize
  pure { x with size := i 0 }

/-! ## Buffer management -/

/-- `compact!`, `base/iobuffer.jl:677-689`. -/
def compact : M I := do
  let io ← get
  let offset := getOffset io
  let (a, b) ← lift (getUsedSpan io)
  let deleted := a - i 1
  let compacted := deleted - offset
  if deleted.val = 0 then return i 0
  let data ← lift (copyto io.data (i 1) io.data (deleted + i 1) (rangeLength a b))
  set { io with data, oc := -getCompacted io - compacted, ptr := io.ptr - deleted,
                size := io.size - deleted }
  return deleted

/-- `_resize!`, `base/iobuffer.jl:536-556`; neither `Memory` nor the other modelled vector
types support `resize!`. -/
def resize (newSize : I) (exact : Bool) : M Unit := do
  let io ← get
  let oldData := io.data
  let newSize := if exact then newSize else imin io.maxsize (overallocation newSize)
  let (a, b) ← lift (getUsedSpan io)
  let deleted := a - i 1
  let compacted := deleted - getOffset io
  let newData ← lift (similarData io newSize)
  set { io with data := newData }
  if newSize.val = 0 then return
  let lenUsed := rangeLength a b
  let newData ← if lenUsed.val = 0 then pure newData else lift (copyto newData (i 1) oldData a lenUsed)
  set { io with data := newData, oc := -getCompacted io - compacted, ptr := io.ptr - deleted,
                size := lenUsed }

/-- `ensureroom_reallocate`, `base/iobuffer.jl:618-624`. -/
def ensureroomReallocate (nshort : U) : M Unit := do
  let io ← get
  if !io.writable then throwArg "ensureroom failed, IOBuffer is not writeable"
  let d ← lift (similarData io (imin io.maxsize (JInt.rem .i64 nshort)))
  set { io with data := d, reinit := false, oc := -getCompacted io }

/-- `ensureroom_slowpath`, `base/iobuffer.jl:627-659`. -/
def ensureroomSlowpath (nshort : U) (available : I) : M Unit := do
  let io ← get
  let (a, _) ← lift (getUsedSpan io)
  let reclaimable := a - i 1
  if reclaimable.val ≥ 32 ∧ reclaimable.val ≥ (io.data.length / 8 : Nat) ∧
      (JInt.rem .u64 (reclaimable + available)).val ≥ nshort.val then
    let _ ← compact
    return
  let n ← lift (toI nshort.val)
  let desired := i io.data.length + n - available
  if desired.val > io.maxsize.val then
    if reclaimable.val ≠ 0 then
      discard compact
    let io ← get
    if io.data.length < io.maxsize.val then resize io.maxsize true
  else
    resize desired false

/-- `ensureroom(io, nshort::UInt)`, `base/iobuffer.jl:599-615`. -/
def ensureroom (nshort : U) : M Unit := do
  let io ← get
  if !io.writable || io.reinit then ensureroomReallocate nshort
  else
    let start := if io.append then io.size else io.ptr - i 1
    let existing := imin (i io.data.length - start) (io.maxsize - (start - getOffset io))
    if existing.val < (JInt.rem .i64 nshort).val then ensureroomSlowpath nshort existing

/-! ## Writing -/

/-- `unsafe_write(to, p, nb)` with `p` pointing at `src`, `base/iobuffer.jl:902-921`;
`write(io, ::Vector{UInt8})` calls it. -/
def unsafeWrite (src : List UInt8) : M I := do
  let nb : U := u src.length
  ensureroom nb
  let io ← get
  let size := io.size
  let append := io.append
  let ptr := if append then size + i 1 else io.ptr
  let start := ptr - i 1
  let inner := imin (i io.data.length - start) (io.maxsize - (start - getOffset io))
  let toWrite := imax (i 0) (JInt.rem .i64 (uminU nb (JInt.rem .u64 inner)))
  let data ← lift (writeAt io.isMem io.data ptr (src.take toWrite.val.toNat))
  set { io with data, size := imax size (start + toWrite),
                ptr := if append then io.ptr else ptr + toWrite }
  return toWrite

/-- `write(to, a::UInt8)`, `base/iobuffer.jl:948-963`. -/
def writeByte (a : UInt8) : M I := do
  ensureroom (u 1)
  let io ← get
  let ptr := if io.append then io.size + i 1 else io.ptr
  if (ptr - getOffset io).val > io.maxsize.val then return i 0
  let data ← lift (setChecked io.data ptr a)
  set { io with data, size := imax io.size ptr, ptr := if io.append then io.ptr else io.ptr + i 1 }
  return i 1

/-! ## Reading -/

def throwNotReadable {α} : M α := throwArg "read failed, IOBuffer is not readable"

/-- `read(from, UInt8)`, `base/iobuffer.jl:438-448`. -/
def readByte : M UInt8 := do
  let io ← get
  if !io.readable then throwNotReadable
  if io.ptr.val > io.size.val then throw .eofError
  let b ← lift (readAt io.data io.ptr 1)
  set { io with ptr := io.ptr + i 1 }
  return b.headD 0

/-- `peek(from, UInt8)`, `base/iobuffer.jl:450-456`. -/
def peekByte : M UInt8 := do
  let io ← get
  if !io.readable then throwNotReadable
  if io.ptr.val > io.size.val then throw .eofError
  lift (getChecked io.data io.ptr)

/-- `unsafe_read(from, p, nb)`, `base/iobuffer.jl:349-359`: the bytes stored at `p`. -/
def unsafeRead (nb : U) : M (List UInt8) := do
  let io ← get
  if !io.readable then throwNotReadable
  let avail := JInt.rem .u64 (bytesavailable io)
  let adv := uminU avail nb
  let bytes ← lift (readAt io.data io.ptr adv.val.toNat)
  let np ← lift (toI (JInt.rem .u64 io.ptr + adv).val)
  set { io with ptr := np }
  if nb.val > avail.val then throw .eofError
  return bytes

/-- `read!(io, A)` for `A::Vector{UInt8}` of length `n` (`base/io.jl:1019-1022, 998`). -/
def readBang (n : Nat) : M (List UInt8) := do
  let nb ← lift (toU n)
  unsafeRead nb

/-- `read(io, nb::Int)`, `base/iobuffer.jl:982`. -/
def readN (nb : I) : M (List UInt8) := do
  let io ← get
  let n := imin nb (bytesavailable io)
  let d ← lift (stringMemory n)
  readBang d.length

/-- `read(io)` and `readavailable(io)`, `base/iobuffer.jl:977-980`. -/
def readAll : M (List UInt8) := do
  let io ← get
  let d ← lift (stringMemory (bytesavailable io))
  readBang d.length

/-- `readbytes!(io, b, nb::Int)`, `base/iobuffer.jl:967-976`: the count and the bytes read
into `b`. -/
def readbytes (nb : I) : M (I × List UInt8) := do
  let io ← get
  if !io.readable then throwNotReadable
  let toRead := imin nb (bytesavailable io)
  let n ← lift (toU toRead.val)
  let bytes ← unsafeRead n
  return (toRead, bytes)

/-- `peek(from, T)` for an `nb`-byte bits type `T`, `base/iobuffer.jl:418-430`: its
little-endian bytes. -/
def peekT (nb : Nat) : M (List UInt8) := do
  let io ← get
  if !io.readable then throwNotReadable
  if (nb : Int) > (bytesavailable io).val then throw .eofError
  lift (readAt io.data io.ptr nb)

/-- `read(from, T)` for an `nb`-byte bits type `T`, `base/iobuffer.jl:432-436`. -/
def readT (nb : Nat) : M (List UInt8) := do
  let x ← peekT nb
  modify fun io => { io with ptr := io.ptr + i nb }
  return x

/-! ## Seeking and marks -/

/-- `seek(io, n::Int)`, `base/iobuffer.jl:512-524`. -/
def seek (n : I) : M Unit := do
  let io ← get
  if !io.seekable then
    if !ismarked io then throwArg "seek failed, IOBuffer is not seekable and is not marked"
    if n ≠ io.mark then throwArg "seek failed, IOBuffer is not seekable and n != mark"
  let maxPtr := io.size + i 1
  let minPtr := getOffset io + i 1
  set { io with ptr := clampI (translateSeekPosition io n) minPtr maxPtr }

/-- `seek(io, n::Integer)`, `base/iobuffer.jl:496-498`. -/
def seekAny (n : Int) : M Unit := seek (clampToI n)

/-- `seekstart`, `base/iostream.jl:185`. -/
def seekstart : M Unit := seek (i 0)

/-- `seekend`, `base/iobuffer.jl:526-529`. -/
def seekend : M Unit := modify fun io => { io with ptr := io.size + i 1 }

/-- `skip(io, n::Integer)`, `base/iobuffer.jl:475-494`. -/
def skip (n : Int) : M Unit := do
  let n := clampToI n
  if n.val < 0 then
    let io ← get
    seek (clampToI ((position io).val + n.val))
  else
    let io ← get
    let nmax := io.size + i 1 - io.ptr
    set { io with ptr := io.ptr + imin n nmax }

/-- `mark`, `base/io.jl:1575-1577`. -/
def mark : M I := do
  let io ← get
  set { io with mark := position io }
  return position io

/-- `unmark`, `base/io.jl:1586-1590`. -/
def unmark : M Bool := do
  let io ← get
  if !ismarked io then return false
  set { io with mark := i (-1) }
  return true

/-- `reset`, `base/io.jl:1600-1606`. -/
def reset : M I := do
  let io ← get
  if !ismarked io then throwArg "IOBuffer not marked"
  let m := io.mark
  seek m
  modify fun io => { io with mark := i (-1) }
  return m

/-! ## Truncation and taking -/

/-- `truncate(io, n::Int)`, `base/iobuffer.jl:558-593`. -/
def truncate (n : I) : M Unit := do
  let io ← get
  if !io.writable then throwArg "truncate failed, IOBuffer is not writeable"
  if !io.seekable then throwArg "truncate failed, IOBuffer is not seekable"
  if n.val < 0 then throwArg "truncate failed, n bytes must be ≥ 0"
  if n.val > io.maxsize.val then throwArg "truncate failed, n bytes exceeds IOBuffer maxsize"
  let offset := getOffset io
  let currentSize := io.size - offset
  if io.reinit then
    let d ← lift (similarData io n)
    set { io with data := List.replicate d.length 0, reinit := false, size := n }
  else if n.val < currentSize.val then
    let io := if (translateSeekPosition io io.mark).val > (n + offset).val then { io with mark := i (-1) } else io
    set { io with size := n + offset, ptr := imin io.ptr (n + offset + i 1) }
  else if n.val > currentSize.val then
    if (n + offset).val > io.maxsize.val then
      discard compact
    resize (n + getOffset (← get)) false
    let io ← get
    let hi := imin (i io.data.length) (n + getOffset io)
    let data ← lift (fillZero io.data (io.size + i 1) hi)
    set { io with data, size := hi }

/-- The reset at the end of `take!`/`takestring!` for a writable buffer. -/
def resetTaken (io : IOBuf) : IOBuf := { io with reinit := true, ptr := i 1, size := i 0, oc := i 0 }

/-- `wrap(Array, memoryref(data, k), n)`: the `n` bytes from index `k`. -/
def wrapBytes (d : List UInt8) (k n : I) : Except IOErr (List UInt8) :=
  if 1 ≤ k.val ∧ k.val + n.val - 1 ≤ d.length then .ok (slice d k.val (k.val + n.val - 1))
  else .error (.jl .boundsError)

/-- `take!`: `base/iobuffer.jl:758-786` for an `IOBuffer`, `731-753` otherwise. -/
def take : M (List UInt8) := do
  modify fun io => { io with mark := i (-1) }
  let io ← get
  let data ←
    if io.isMem then
      if io.seekable then
        let nbytes := filesize io
        if nbytes.val = 0 ∨ io.reinit then pure []
        else lift (wrapBytes io.data (getOffset io + i 1) nbytes)
      else
        let nbytes := bytesavailable io
        if nbytes.val = 0 then pure []
        else if io.writable then lift (wrapBytes io.data io.ptr nbytes)
        else throw (.errorException "Unreachable IOBuffer state")
    else
      if io.seekable then
        let offset := getOffset io
        let nbytes := io.size - offset
        let d ← lift (stringMemory nbytes)
        lift (copyto d (i 1) io.data (offset + i 1) nbytes)
      else
        let d ← lift (stringMemory (bytesavailable io))
        readBang d.length
  let io ← get
  if io.writable then set (resetTaken io)
  return data

/-- `takestring!`, `base/iobuffer.jl:795-862`: the bytes of the returned `String`. -/
def takestring : M (List UInt8) := do
  let io ← get
  if !io.isMem then
    let r ← take
    return r
  if io.reinit then return []
  if io.writable then
    let (a, b) ← lift (getUsedSpan io)
    let s := if (rangeLength a b).val = 0 then [] else slice io.data a.val b.val
    set { resetTaken io with mark := i (-1) }
    return s
  else
    let (a, b) ← lift (getUsedSpan io)
    return slice io.data a.val b.val

/-! ## Delimited reading -/

/-- `view(io.data, io.ptr:io.size)`. -/
def pending (io : IOBuf) : Except IOErr (List UInt8) :=
  if io.size.val < io.ptr.val then .ok []
  else if 1 ≤ io.ptr.val ∧ io.size.val ≤ io.data.length then .ok (slice io.data io.ptr.val io.size.val)
  else .error (.jl .boundsError)

/-- `something(findfirst(==(delim), d), length(d))`. -/
def findOrLen (d : List UInt8) (delim : UInt8) : Nat :=
  match d.idxOf? delim with
  | some k => k + 1
  | none => d.length

/-- `readuntil(io, delim::UInt8; keep)`, i.e. `copyuntil(IOBuffer(), io, delim; keep)`,
`base/io.jl:624-626`, `base/iobuffer.jl:993-1008`: the bytes copied. -/
def readuntil (delim : UInt8) (keep : Bool) : M (List UInt8) := do
  let io ← get
  let d ← lift (pending io)
  let nread := findOrLen d delim
  let nout := if !keep ∧ nread > 0 ∧ d.getD (nread - 1) 0 = delim then nread - 1 else nread
  set { io with ptr := io.ptr + i nread }
  return d.take nout

/-- `readline(io; keep)`, i.e. `_copyline(IOBuffer(), io; keep)`, `base/io.jl:714-716`,
`base/iobuffer.jl:1057-1074`: the bytes of the line. -/
def readline (keep : Bool) : M (List UInt8) := do
  let io ← get
  let d ← lift (pending io)
  let nread := findOrLen d 0x0a
  let nout :=
    if !keep ∧ nread > 0 ∧ d.getD (nread - 1) 0 = 0x0a then
      if nread - 1 > 0 ∧ d.getD (nread - 2) 0 = 0x0d then nread - 2 else nread - 1
    else nread
  set { io with ptr := io.ptr + i nread }
  return d.take nout

/-- `occursin(delim::UInt8, buf)`, `base/iobuffer.jl:984-986`. -/
def occursin (delim : UInt8) (io : IOBuf) : Except IOErr Bool := do
  let d ← pending io
  pure (d.contains delim)

/-- `copyline(out::GenericIOBuffer, s::IO; keep)` for a stream `s` that is not a
`GenericIOBuffer`, `base/iobuffer.jl:1010-1055`. `line` is what
`copyuntil(_, s, 0x0a; keep=true)` delivers: the bytes of `s` up to and including the
first newline, written with one `write`. -/
def copylineFrom (line : List UInt8) (keep : Bool) : M Unit := do
  let out ← get
  if !out.append ∧ out.ptr.val < (out.size + i 1).val then
    let v := line
    let v := if !keep ∧ v.length > 1 ∧ v.getLast? = some 0x0a then v.dropLast else v
    let v := if !keep ∧ v.length > 1 ∧ v.getLast? = some 0x0d then v.dropLast else v
    let _ ← unsafeWrite v
  else
    let _ ← unsafeWrite line
    let out ← get
    let k := out.size
    if keep then return
    if k = out.oc then return
    if (← lift (getChecked out.data k)) ≠ 0x0a then return
    let k ← if k.val < 2 then pure (k - i 1) else do
      let c ← lift (getChecked out.data (k - i 1))
      pure (if c ≠ 0x0d then k - i 1 else k - i 2)
    set { out with size := k, ptr := if out.append then out.ptr else k + i 1 }

/-- `peek(s, T)` for a one-byte `T` other than `UInt8` (e.g. `Int8`), the generic method
`base/io.jl:382-388`: `mark`, `read`, then `reset` in a `finally`. -/
def peekGeneric : M UInt8 := do
  let _ ← mark
  let r ← tryCatch readByte (fun e => do let _ ← reset; throw e)
  let _ ← reset
  return r

/-! ## Closing -/

/-- `closewrite`, `base/iobuffer.jl:693-696`. -/
def closewrite : M Unit := modify fun io => { io with writable := false }

/-- The field assignments at the end of `close`, `base/iobuffer.jl:702-709`. -/
def closedState (io : IOBuf) : IOBuf :=
  { io with readable := false, writable := false, seekable := false, size := i 0,
            maxsize := i 0, ptr := i 1, mark := i (-1), oc := -getCompacted io }

/-- `close`, `base/iobuffer.jl:698-711`. -/
def close : M Unit := do
  let io ← get
  if io.writable ∧ !io.reinit then resize (i 0) true
  modify closedState

end JuliaLean.IOBuffers

namespace JuliaLean.IOCov.Io

/-- `readline(s)` (the `IOBuffer` method of `copyline`, `base/iobuffer.jl:1010-1055`): the
bytes before the first `'\n'`, with one `'\r'` before that newline removed. -/
def readlineRef (inp : Bytes) : Bytes :=
  let line := inp.takeWhile (· != 0x0a)
  if 0x0a ∈ inp ∧ line.getLast? = some 0x0d then line.dropLast else line

end JuliaLean.IOCov.Io

namespace JuliaLean.IOCov.IOBuf

/-- The `GenericIOBuffer` fields used by `show` and `position`. -/
structure Buf where
  size : Int
  ptr : Int
  offsetOrCompacted : Int
  deriving DecidableEq, Repr

/-- `get_offset(io) = max(0, io.offset_or_compacted)`, line 163. -/
def getOffset (b : Buf) : Int := max 0 b.offsetOrCompacted
/-- `get_compacted(io) = max(0, -io.offset_or_compacted)`, line 164. -/
def getCompacted (b : Buf) : Int := max 0 (-b.offsetOrCompacted)
/-- `position(io) = io.ptr - io.offset_or_compacted - 1`, lines 470-473. -/
def position (b : Buf) : Int := b.ptr - b.offsetOrCompacted - 1
/-- The `size=` and `ptr=` values printed by `show(io, b)`, lines 334-342. -/
def showSize (b : Buf) : Int := b.size - getOffset b
def showPtr (b : Buf) : Int := b.ptr - getOffset b

end JuliaLean.IOCov.IOBuf

namespace JuliaLean.IOCov.IOBufferRemaining

open JuliaLean
open JuliaLean.IOBuffers

/-! ## Constructors and accessors -/

/-- `_new_generic_iobuffer`, `base/iobuffer.jl:96-107`. -/
def newGeneric (data : List UInt8) (isMem readable writable seekable append : Bool)
    (maxsize : I) : IOBuf := newBuf data isMem readable writable seekable append maxsize

/-- `GenericIOBuffer{T}(...)`, `base/iobuffer.jl:110-130`. -/
def genericTyped (data : DataArg) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr IOBuf :=
  genericIOBuffer data readable writable seekable append maxsize truncate

/-- Untyped `GenericIOBuffer(...)`, `base/iobuffer.jl:134-137`. -/
def genericUntyped (data : DataArg) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr IOBuf :=
  genericTyped data readable writable seekable append maxsize truncate

/-- `GenericIOBuffer(data::Vector{UInt8}, ...)`, `base/iobuffer.jl:141-161`. -/
def genericVector (v : Vec) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr IOBuf :=
  genericIOBuffer (.vec v) readable writable seekable append maxsize truncate

/-- `get_offset`, `base/iobuffer.jl:163`. -/
def getOffsetMethod (io : IOBuf) : I := getOffset io
/-- `get_compacted`, `base/iobuffer.jl:164`. -/
def getCompactedMethod (io : IOBuf) : I := getCompacted io
/-- `StringMemory`, `base/iobuffer.jl:167`. -/
def stringMemoryMethod (n : Int) : Except IOErr (List UInt8) := toI n >>= stringMemory
/-- `StringVector`, `base/iobuffer.jl:168`. -/
def stringVectorMethod (n : Int) : Except IOErr (List UInt8) := stringMemoryMethod n

/-- `IOBuffer(data; ...)`, `base/iobuffer.jl:230-244`. -/
def ioBufferDataMethod (data : DataArg) (read write append truncate : Option Bool)
    (maxsize : Int) : Except IOErr IOBuf := iobufferData data read write append truncate maxsize

/-- `IOBuffer(; ...)`, `base/iobuffer.jl:246-270`. -/
def ioBufferEmptyMethod (read write append truncate : Option Bool) (maxsize : Int)
    (sizehint : Option Int) : Except IOErr IOBuf :=
  iobufferEmpty read write append truncate maxsize sizehint

/-- `PipeBuffer(data; maxsize::Int)`, `base/iobuffer.jl:284-285`. -/
def pipeBufferMethod (data : DataArg) (maxsize : Int) : Except IOErr IOBuf :=
  pipeBuffer data .i64 maxsize

/-- `_truncated_pipebuffer`, `base/iobuffer.jl:289-294`. -/
def truncatedPipeBuffer (data : DataArg) (maxsize : Int) : Except IOErr IOBuf := do
  let buf <- pipeBuffer data .i64 (2 ^ 63 - 1)
  pure { buf with size := getOffset buf, maxsize := i maxsize }

/-- `_similar_data(b::IOBuffer, len)`, `base/iobuffer.jl:297`. -/
def similarDataMethod (b : IOBuf) (len : I) : Except IOErr (List UInt8) :=
  stringMemory len

/-- `copy(b::GenericIOBuffer)`, `base/iobuffer.jl:302-332`. -/
def copyBuffer (b : IOBuf) : Except IOErr IOBuf := do
  if b.reinit then
    let data <- similarData b (i 0)
    genericIOBuffer (if b.isMem then .mem data else .other data) b.readable b.writable
      b.seekable b.append b.maxsize.val false
  else if b.writable then
    let used <- getUsedSpan b
    let compacted := used.1 - getOffset b - i 1
    let len := rangeLength used.1 used.2
    let data0 <- similarData b len
    let data <- copyto data0 (i 1) b.data used.1 len
    let ret <- genericIOBuffer (if b.isMem then .mem data else .other data) b.readable b.writable
      b.seekable b.append b.maxsize.val false
    pure (IOBuf.mk ret.data ret.isMem ret.reinit ret.readable ret.writable ret.seekable
      ret.append len ret.maxsize (b.ptr - used.1 + i 1) (-(getCompacted b) - compacted) b.mark)
  else
    pure (IOBuf.mk b.data b.isMem false b.readable b.writable b.seekable b.append
      (i b.data.length) b.maxsize b.ptr b.oc b.mark)

/-! ## Reading fixed-width values -/

/-- `_throw_not_readable`, `base/iobuffer.jl:344-347`. -/
def throwNotReadableMethod {alpha : Type} : Except IOErr alpha :=
  .error (.jl (.argumentError "read failed, IOBuffer is not readable"))

/-- `unsafe_read!` for an abstract byte vector, `base/iobuffer.jl:361-365`. -/
def unsafeReadAbstract (src : List UInt8) (so : I) (nbytes : Nat) : Except IOErr (List UInt8) :=
  readAt src so nbytes

/-- Dense `unsafe_read!`, `base/iobuffer.jl:375-378`. -/
def unsafeReadDense (src : List UInt8) (so : I) (nbytes : Nat) : Except IOErr (List UInt8) :=
  readAt src so nbytes

/-- Little-endian value assembled by `load_from_array`, `base/iobuffer.jl:394-404`. -/
def loadFromArray (data : List UInt8) (start nbytes : Nat) : Nat :=
  (List.range nbytes).foldl (fun x k => x ||| ((data.getD (start - 1 + k) 0).toNat <<< (8 * k))) 0

/-- Generic-vector `peek(from, T::MultiByteBitNumberType)`, `base/iobuffer.jl:406-414`. -/
def peekMultiGeneric (src : IOBuf) (nbytes : Nat) : Except IOErr Nat :=
  if !src.readable then throwNotReadableMethod
  else if nbytes > (bytesavailable src).val then .error .eofError
  else .ok (loadFromArray src.data src.ptr.val.toNat nbytes)

/-- Dense-vector `peek(from, T::MultiByteBitNumberType)`, `base/iobuffer.jl:418-430`. -/
def peekMultiDense (src : IOBuf) (nbytes : Nat) : Except IOErr (List UInt8) :=
  match (peekT nbytes).run src with
  | .ok x _ => .ok x
  | .error e _ => .error e

/-- `read(from, T::MultiByteBitNumberType)`, `base/iobuffer.jl:432-436`. -/
def readMulti (src : IOBuf) (nbytes : Nat) : EStateM.Result IOErr IOBuf (List UInt8) :=
  (readT nbytes).run src

/-- `read(from, ::Type{Ptr{T}})`, `base/iobuffer.jl:458`. -/
def readPtrMethod (src : IOBuf) : EStateM.Result IOErr IOBuf (List UInt8) :=
  (readT 8).run src

/-- `isreadable(io::GenericIOBuffer)`, `base/iobuffer.jl:460`. -/
def isreadableMethod (io : IOBuf) : Bool := io.readable
/-- `iswritable(io::GenericIOBuffer)`, `base/iobuffer.jl:461`. -/
def iswritableMethod (io : IOBuf) : Bool := io.writable

/-! ## Seeking and room management -/

/-- `skip(io, n::Int)`, `base/iobuffer.jl:479-494`. -/
def skipIntMethod (io : IOBuf) (n : Int) : EStateM.Result IOErr IOBuf Unit :=
  (skip n).run io
/-- `translate_seek_position`, `base/iobuffer.jl:500-510`. -/
def translateSeekMethod (io : IOBuf) (n : I) : I := translateSeekPosition io n
/-- `seek(io, n::Int)`, `base/iobuffer.jl:512-524`. -/
def seekIntMethod (io : IOBuf) (n : I) : EStateM.Result IOErr IOBuf Unit := (seek n).run io
/-- `seekend`, `base/iobuffer.jl:526-529`. -/
def seekendMethod (io : IOBuf) : EStateM.Result IOErr IOBuf Unit := seekend.run io
/-- `ensureroom(io, nshort::Int)`, `base/iobuffer.jl:597`. -/
def ensureroomInt (io : IOBuf) (nshort : Int) : EStateM.Result IOErr IOBuf Unit :=
  (ensureroom (u nshort)).run io
/-- `ensureroom(io, nshort::UInt)`, `base/iobuffer.jl:599-615`. -/
def ensureroomUInt (io : IOBuf) (nshort : U) : EStateM.Result IOErr IOBuf Unit :=
  (ensureroom nshort).run io
/-- `ensureroom_reallocate`, `base/iobuffer.jl:618-624`. -/
def ensureroomReallocateMethod (io : IOBuf) (nshort : U) : EStateM.Result IOErr IOBuf Unit :=
  (ensureroomReallocate nshort).run io

/-! ## Close and take -/

/-- `close`, `base/iobuffer.jl:698-711`. -/
def closeMethod (io : IOBuf) : EStateM.Result IOErr IOBuf Unit := close.run io
/-- `isopen`, `base/iobuffer.jl:713`. -/
def isopenMethod (io : IOBuf) : Bool :=
  io.readable || io.writable || io.seekable || (bytesavailable io).val > 0
/-- Generic `take!`, `base/iobuffer.jl:731-753`. -/
def takeGeneric (io : IOBuf) : EStateM.Result IOErr IOBuf (List UInt8) := take.run io

/-- `unsafe_takestring!`, `base/iobuffer.jl:795-809`, as returned bytes. -/
def unsafeTakestring (io : IOBuf) : Except IOErr (List UInt8) := do
  let used <- getUsedSpan io
  let nbytes := rangeLength used.1 used.2
  if nbytes.val = 0 then pure []
  else pure (slice io.data used.1.val used.2.val)

/-- Generic `takestring!`, `base/iobuffer.jl:862`. -/
def takestringGeneric (io : IOBuf) : EStateM.Result IOErr IOBuf (List UInt8) := take.run io

/-- `_unsafe_take!`, `base/iobuffer.jl:876-884`. -/
def unsafeTake (io : IOBuf) : List UInt8 :=
  let offset := getOffset io
  slice io.data (offset.val + 1) io.size.val

/-! ## Transfer and byte operations -/

/-- `write(to::IO, from::GenericIOBuffer)`, `base/iobuffer.jl:886-897`. -/
def writeFromBuffer (to src : IOBuf) : Except IOErr (I × IOBuf × IOBuf) := do
  if to = src then .error (.jl (.argumentError "Writing all content fron an IOBuffer into itself in invalid"))
  else if !src.readable then throwNotReadableMethod
  else
    let bytes <- pending src
    match (unsafeWrite bytes).run to with
    | .error e to' => .error e
    | .ok written to' => .ok (written, to', { src with ptr := src.size + i 1 })

/-- Abstract-vector `_unsafe_write`, `base/iobuffer.jl:923-928`. -/
def unsafeWriteAbstract (data : List UInt8) (start : I) (bytes : List UInt8) : Except IOErr (List UInt8) :=
  writeAt false data start bytes
/-- Dense-vector `_unsafe_write`, `base/iobuffer.jl:930-946`. -/
def unsafeWriteDense (data : List UInt8) (start : I) (bytes : List UInt8) : Except IOErr (List UInt8) :=
  writeAt true data start bytes
/-- `write(to::GenericIOBuffer, a::UInt8)`, `base/iobuffer.jl:948-963`. -/
def writeByteMethod (io : IOBuf) (a : UInt8) : EStateM.Result IOErr IOBuf I :=
  (writeByte a).run io
/-- Default-argument `readbytes!`, `base/iobuffer.jl:965`. -/
def readbytesConvert (io : IOBuf) (nb : Int) : EStateM.Result IOErr IOBuf (I × List UInt8) :=
  (readbytes (i nb)).run io
/-- `readbytes!(..., nb::Int)`, `base/iobuffer.jl:967-976`. -/
def readbytesInt (io : IOBuf) (nb : I) : EStateM.Result IOErr IOBuf (I × List UInt8) :=
  (readbytes nb).run io
/-- `readavailable`, `base/iobuffer.jl:980`. -/
def readavailableMethod (io : IOBuf) : EStateM.Result IOErr IOBuf (List UInt8) := readAll.run io
/-- `read(io, nb::Integer)`, `base/iobuffer.jl:982`. -/
def readCountMethod (io : IOBuf) (nb : I) : EStateM.Result IOErr IOBuf (List UInt8) :=
  (readN nb).run io

/-! ## Line and checksum methods -/

/-- `copyline(out::GenericIOBuffer, s::IO)`, `base/iobuffer.jl:1010-1055`.
`line` is the result of the source `copyuntil(..., keep=true)` call. -/
def copylineGenericOut (out : IOBuf) (line : List UInt8) (keep : Bool) :
    EStateM.Result IOErr IOBuf Unit := (copylineFrom line keep).run out

/-- `copyline(out::IO, io::GenericIOBuffer)`, `base/iobuffer.jl:1079`. -/
def copylineGenericIn (io : IOBuf) (keep : Bool) : EStateM.Result IOErr IOBuf (List UInt8) :=
  (readline keep).run io
/-- `copyline(out::GenericIOBuffer, io::GenericIOBuffer)`, `base/iobuffer.jl:1080`. -/
def copylineGenericBoth (out io : IOBuf) (keep : Bool) :
    Except IOErr (IOBuf × IOBuf) :=
  match (readline keep).run io with
  | .error e io' => .error e
  | .ok line io' =>
      match (unsafeWrite line).run out with
      | .error e _ => .error e
      | .ok _ out' => .ok (out', io')

/-- `_crc32c(io, nb, crc)`, `base/iobuffer.jl:1084-1092`. -/
def crc32cCount (crcFn : List UInt8 -> UInt32 -> UInt32) (io : IOBuf)
    (nb : Int) (crc : UInt32) : Except IOErr (UInt32 × IOBuf) := do
  if nb < 0 then .error (.jl (.argumentError "number of bytes to checksum must be >= 0"))
  else if !io.readable then throwNotReadableMethod
  else
    let n := min nb (bytesavailable io).val
    if n = 0 then pure (crc, io)
    else
      let bytes := slice io.data io.ptr.val (io.ptr.val + n - 1)
      pure (crcFn bytes crc, { io with ptr := io.ptr + i n })

/-- `_crc32c(io, crc)`, `base/iobuffer.jl:1093`. -/
def crc32cAll (crcFn : List UInt8 -> UInt32 -> UInt32) (io : IOBuf) (crc : UInt32) :
    Except IOErr (UInt32 × IOBuf) := crc32cCount crcFn io (bytesavailable io).val crc


end JuliaLean.IOCov.IOBufferRemaining
