import JuliaLean.Core

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
  | .eofError => "EOFError"
  | .errorException _ => "ErrorException"
  | .typeError => "TypeError"
  | .outOfBounds => "UB"
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
  match JInt.convert .i64 x with
  | .ok v => .ok v
  | .error e => .error (.jl e)

/-- `convert(UInt, x)`. -/
def toU (x : Int) : Except IOErr U :=
  match JInt.convert .u64 x with
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
  (io.reinit → io.size = i 0 ∧ io.ptr = i 1 ∧ io.offset = i 0 ∧ io.mark = i (-1))
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

/-- `IOBuffer(data; read, write, append, truncate, maxsize)`, `base/iobuffer.jl:230-244`
(no `sizehint`). -/
def iobufferData (data : DataArg) (read write append truncate : Option Bool) (maxsize : Int := 2 ^ 63 - 1) :
    Except IOErr BufferState :=
  let f := openFlags read write none truncate append
  genericIOBuffer data f.read f.write true f.append maxsize f.truncate

/-- `IOBuffer(; read=true, write=true, append, truncate=true, maxsize, sizehint)`,
`base/iobuffer.jl:246-270`. -/
def iobufferEmpty (read write append truncate : Option Bool) (maxsize : Int := 2 ^ 63 - 1)
    (sizehint : Option Int := none) : Except IOErr BufferState := do
  let mz ← toI maxsize
  if mz.val < 0 then .error (.jl (.argumentError "negative maxsize"))
  let size ← match sizehint with
    | some s => do let s ← toI s; pure (imin mz (imax (i 0) s))
    | none => pure (imin mz (i 32))
  let f := openFlags read write none truncate append
  let d ← stringMemory size
  pure { newBuf d true f.read f.write true f.append mz with size := i 0 }

/-- `IOBuffer()`. -/
def iobuffer : Except IOErr BufferState := iobufferEmpty (some true) (some true) none (some true)

/-- `IOBuffer(str::String)`, `base/strings/io.jl:306`. -/
def iobufferString (s : List UInt8) : Except IOErr BufferState :=
  iobufferData (.vec ⟨s, 0, s.length⟩) none none none none

/-- `PipeBuffer(data=Memory{UInt8}(); maxsize::Int=typemax(Int))`, `base/iobuffer.jl:284-285`.
The keyword is declared `::Int`, so another integer type `t` is a `TypeError`. -/
def pipeBuffer (data : DataArg := .mem []) (t : IntTy := .i64) (maxsize : Int := 2 ^ 63 - 1) :
    Except IOErr BufferState :=
  if t ≠ .i64 then .error .typeError
  else genericIOBuffer data true true false true maxsize false

/-- `PipeBuffer(maxsize::Integer)`, `base/iobuffer.jl:286`. -/
def pipeBufferN (t : IntTy) (maxsize : Int) : Except IOErr BufferState := do
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
def source_new_generic_iobuffer {T : Type} (data : T) (dataBytes : T → List UInt8)
    (isMemory : T → Bool) (readable writable seekable append : Bool) (maxsize : I) : BufferState :=
  let bytes := dataBytes data
  { data := bytes, isMemory := isMemory data, reinit := false, readable, writable, seekable, append,
    size := i bytes.length, maxsize, ptr := i 1, offset := i 0, mark := i (-1) }

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
def source_GenericIOBuffer_typed (requireOneBased : DataArg → Except IOErr Unit)
    (data : DataArg) (readable writable seekable append : Bool) (maxsize : Int)
    (truncate : Bool) : Except IOErr BufferState := do
  let _ ← requireOneBased data
  let mz ← toI maxsize
  let len := (dataBytes data).length
  if !truncate && mz.val < len then
    throw (.jl (.argumentError "maxsize must not be smaller than data length"))
  let buf := source_new_generic_iobuffer data dataBytes dataIsMemory readable writable seekable append mz
  if truncate then pure { buf with size := buf.offset } else pure buf

/--
Julia source: base/iobuffer.jl:134-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function GenericIOBuffer(data::T, readable::Bool, writable::Bool, seekable::Bool, append::Bool,
                         maxsize::Integer, truncate::Bool) where T<:AbstractVector{UInt8}
    GenericIOBuffer{T}(data, readable, writable, seekable, append, maxsize, truncate)
end
```
-/
def source_GenericIOBuffer (data : DataArg) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr BufferState :=
  source_GenericIOBuffer_typed (fun _ => .ok ()) data readable writable seekable append maxsize truncate

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
def source_GenericIOBuffer_Vector (v : Vec) (readable writable seekable append : Bool)
    (maxsize : Int) (truncate : Bool) : Except IOErr BufferState := do
  let mz ← toI maxsize
  if !truncate && mz.val < v.len then
    throw (.jl (.argumentError "maxsize must not be smaller than data length"))
  let buf := source_new_generic_iobuffer v.mem id (fun _ => true)
    readable writable seekable append mz
  let buf := { buf with offset := i v.off, ptr := i (v.off + 1) }
  if truncate then pure { buf with size := i v.off }
  else pure { buf with size := i (v.len + v.off) }

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
def source_StringMemory (stringN : Int → Except IOErr (List UInt8))
    (unsafeWrap : List UInt8 → Except IOErr (List UInt8)) (n : Int) : Except IOErr (List UInt8) := do
  let p ← stringN n
  unsafeWrap p

/--
Julia source: base/iobuffer.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
StringVector(n::Integer) = wrap(Array, StringMemory(n))
```
-/
def source_StringVector (stringN : Int → Except IOErr (List UInt8))
    (unsafeWrap wrapArray : List UInt8 → Except IOErr (List UInt8)) (n : Int) :
    Except IOErr (List UInt8) := do
  let memory ← source_StringMemory stringN unsafeWrap n
  wrapArray memory

def stringNModel (n : Int) : Except IOErr (List UInt8) :=
  if n < 0 || n > 2 ^ 64 - 1 then .error (.jl (.inexactError "convert"))
  else .ok (List.replicate n.toNat 0)

def unsafeWrapModel (memory : List UInt8) : Except IOErr (List UInt8) := .ok memory

def wrapArrayModel (memory : List UInt8) : Except IOErr (List UInt8) := .ok memory

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
def source_IOBuffer_data (sizehint : DataArg → Int → Except IOErr DataArg)
    (data : DataArg) (read write append truncate : Option Bool) (maxsize : Int)
    (sizeHint : Option Int) : Except IOErr BufferState := do
  let data ← match sizeHint with
    | none => pure data
    | some n => sizehint data n
  let flags := openFlags read write none truncate append
  match data with
  | .vec v => source_GenericIOBuffer_Vector v flags.read flags.write true flags.append maxsize flags.truncate
  | _ => source_GenericIOBuffer data flags.read flags.write true flags.append maxsize flags.truncate

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
def source_IOBuffer_empty (read write append truncate : Option Bool) (maxsize : Int)
    (sizehint : Option Int) : Except IOErr BufferState := do
  let mz ← toI maxsize
  if mz.val < 0 then throw (.jl (.argumentError "negative maxsize"))
  let size ← match sizehint with
    | some n => do
        let n ← toI n
        pure (imin mz (imax (i 0) n))
    | none => pure (imin mz (i 32))
  let flags := openFlags read write none truncate append
  let data ← source_StringMemory stringNModel unsafeWrapModel size.val
  let buf := source_new_generic_iobuffer data id (fun _ => true)
    flags.read flags.write true flags.append mz
  pure { buf with size := i 0 }

/--
Julia source: base/iobuffer.jl:284-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PipeBuffer(data::AbstractVector{UInt8}=Memory{UInt8}(); maxsize::Int = typemax(Int)) =
    GenericIOBuffer(data, true, true, false, true, maxsize, false)
```
-/
def source_PipeBuffer_data (data : DataArg) (maxsize : I) : Except IOErr BufferState :=
  match data with
  | .vec v => source_GenericIOBuffer_Vector v true true false true maxsize.val false
  | _ => source_GenericIOBuffer data true true false true maxsize.val false

/--
Julia source: base/iobuffer.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PipeBuffer(maxsize::Integer) = (x = PipeBuffer(StringMemory(maxsize), maxsize = maxsize); x.size = 0; x)
```
-/
def source_PipeBuffer_maxsize (t : IntTy) (maxsize : Int) : Except IOErr BufferState := do
  let data ← source_StringMemory stringNModel unsafeWrapModel maxsize
  if t != .i64 then throw .typeError
  let x ← source_PipeBuffer_data (.mem data) (i maxsize)
  pure { x with size := i 0 }

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
def source_truncated_pipebuffer (data : DataArg) (maxsize : I) : Except IOErr BufferState := do
  let buf ← source_PipeBuffer_data data imaxval
  pure { buf with size := source_get_offset buf, maxsize := maxsize }

/--
Julia source: base/iobuffer.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_data(b::GenericIOBuffer, len::Int) = similar(b.data, len)
```
-/
def source_similar_data_generic (similar : List UInt8 → I → Except IOErr (List UInt8))
    (b : BufferState) (len : I) : Except IOErr (List UInt8) :=
  similar b.data len

/--
Julia source: base/iobuffer.jl:297-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_similar_data(b::IOBuffer, len::Int) = StringMemory(len)
```
-/
def source_similar_data_IOBuffer (stringMemory : Int → Except IOErr (List UInt8))
    (_b : BufferState) (len : I) : Except IOErr (List UInt8) :=
  stringMemory len.val

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
def source_show {Out : Type} (print : Out → List String → Except IOErr Out) (io : Out) (b : BufferState) :
    Except IOErr Out :=
  print io ["IOBuffer(data=UInt8[...], ", "readable=", toString b.readable, ", ",
    "writable=", toString b.writable, ", ", "seekable=", toString b.seekable, ", ",
    "append=", toString b.append, ", ", "size=", toString (b.size - getOffset b), ", ",
    "maxsize=", if b.maxsize.val = 2 ^ 63 - 1 then "Inf" else toString b.maxsize.val,
    ", ", "ptr=", toString (b.ptr - getOffset b), ", ", "mark=", toString b.mark.val, ")"]

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
def source_unsafe_read {P : Type}
    (unsafeReadBang : P → List UInt8 → I → U → Except IOErr Unit) (p : P) (nb : U) : M Unit := do
  let sourceBuf ← get
  if !sourceBuf.readable then throwNotReadable
  let avail := JInt.rem .u64 (bytesavailable sourceBuf)
  let adv := uminU avail nb
  let _ ← lift (unsafeReadBang p sourceBuf.data sourceBuf.ptr adv)
  modify fun sourceBuf => { sourceBuf with ptr := sourceBuf.ptr + i adv.val }
  if nb.val > avail.val then throw .eofError
  return ()

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
def source_unsafe_read_vector {P Src : Type}
    (load : Src → Int → UInt8) (unsafeStore : P → UInt8 → U → Except IOErr Unit)
    (dest : P) (src : Src) (so : Int) (nbytes : U) : Except IOErr Unit := do
  for k in List.range nbytes.val.toNat do
    let i := k + 1
    let b := load src (so + i - 1)
    let _ ← unsafeStore dest b (u i)
  pure ()

/--
Julia source: base/iobuffer.jl:375-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_read!(dest::Ptr{UInt8}, src::DenseBytes, so::Integer, nbytes::UInt)
    GC.@preserve src unsafe_copyto!(dest, pointer(src, so), nbytes)
    nothing
end
```
-/
def source_unsafe_read_dense {P Src : Type}
    (preserveCopy : Src → P → P → U → Except IOErr Unit)
    (pointer : Src → Int → P) (dest : P) (src : Src) (so : Int) (nbytes : U) :
    Except IOErr Unit := do
  preserveCopy src dest (pointer src so) nbytes

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
def source_load_from_array {T Data : Type} (isFloat : Bool)
    (uintZero unsignedZero : T) (sizeOf : T → Nat) (getByte : Data → Int → UInt8)
    (convertByte : UInt8 → T) (shift : T → Nat → T) (bitOr : T → T → T)
    (ltoh reinterpret : T → T) (data : Data) (sourceBuf : I) : T :=
  let initial := if isFloat then uintZero else unsignedZero
  let x := (List.range (sizeOf initial)).foldl
    (fun x (i : Nat) => bitOr x (shift (convertByte (getByte data (sourceBuf.val + (i : Int)))) (8 * i))) initial
  reinterpret (ltoh x)

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
def source_peek_multibyte {T : Type} (sizeOf : T → Nat)
    (load : BufferState → T → Except IOErr T) (typeValue : T) : M T := do
  let sourceBuf ← get
  if !sourceBuf.readable then throwNotReadable
  let avail := bytesavailable sourceBuf
  let nb := sizeOf typeValue
  if (nb : Int) > avail.val then throw .eofError
  lift (load sourceBuf typeValue)

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
def source_peek_multibyte_dense {T P : Type} (sizeOf : T → Nat)
    (pointer : BufferState → Int → P) (unsafeLoad : P → Except IOErr T)
    (withPreserve : BufferState → (P → Except IOErr T) → Except IOErr T) (typeValue : T) : M T := do
  let sourceBuf ← get
  if !sourceBuf.readable then throwNotReadable
  let avail := bytesavailable sourceBuf
  let nb := sizeOf typeValue
  if (nb : Int) > avail.val then throw .eofError
  lift (withPreserve sourceBuf (fun _ => unsafeLoad (pointer sourceBuf sourceBuf.ptr.val)))

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
def source_read_multibyte {T : Type} (peek : T → M T) (sizeOf : T → Nat)
    (typeValue : T) : M T := do
  let x ← peek typeValue
  modify fun sourceBuf => { sourceBuf with ptr := sourceBuf.ptr + i (sizeOf typeValue) }
  return x

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
def source_read_uint8 : M UInt8 := do
  let sourceBuf ← get
  if !sourceBuf.readable then throwNotReadable
  let ptr := sourceBuf.ptr
  let size := sourceBuf.size
  if ptr.val > size.val then throw .eofError
  let byte ← lift (getUnchecked sourceBuf.data ptr)
  set { sourceBuf with ptr := ptr + i 1 }
  return byte

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
def source_read_pointer {P : Type} (readUInt : M U) (convert : U → P) : M P := do
  convert <$> readUInt

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
def source_skip_integer (skipInt : BufferState → I → M Unit) (io : BufferState) (n : Int) : M Unit :=
  skipInt io (clampToI n)

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
def source_skip (seekInt : I → M Unit) (n : I) : M Unit := do
  if n.val < 0 then
    let io ← get
    let seekto := clampToI ((position io).val + n.val)
    seekInt seekto
  else
    let io ← get
    let nmax := io.size + i 1 - io.ptr
    set { io with ptr := io.ptr + imin n nmax }

/--
Julia source: base/iobuffer.jl:496-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function seek(io::GenericIOBuffer, n::Integer)
    seek(io, clamp(n, Int))
end
```
-/
def source_seek_integer (seekInt : BufferState → I → M Unit) (io : BufferState) (n : Int) : M Unit :=
  seekInt io (clampToI n)

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
def source_translate_seek_position (io : BufferState) (n : I) : I :=
  clampToI (n.val + io.offset.val + 1)

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
def source_seek (n : I) : M Unit := do
  let io ← get
  if !io.seekable then
    if !ismarked io then throwArg "seek failed, IOBuffer is not seekable and is not marked"
    if n ≠ io.mark then throwArg "seek failed, IOBuffer is not seekable and n != mark"
  let maxPtr := io.size + i 1
  let minPtr := getOffset io + i 1
  set { io with ptr := clampI (source_translate_seek_position io n) minPtr maxPtr }

/--
Julia source: base/iobuffer.jl:526-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function seekend(io::GenericIOBuffer)
    io.ptr = io.size+1
    return io
end
```
-/
def source_seekend : M Unit := modify fun io => { io with ptr := io.size + i 1 }

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
def source_resize (isApplicable : Bool) (resizeInPlace : List UInt8 → I → Except IOErr (List UInt8))
    (similar : BufferState → I → Except IOErr (List UInt8)) (exact : Bool) (newSize : I) : M Unit := do
  let io ← get
  let oldData := io.data
  if isApplicable then
    let data ← lift (resizeInPlace oldData newSize)
    set { io with data }
  else
    let newSize := if exact then newSize else imin io.maxsize (overallocation newSize)
    let usedSpan ← lift (getUsedSpan io)
    let deleted := usedSpan.1 - i 1
    let compacted := deleted - getOffset io
    let newData ← lift (similar io newSize)
    set { io with data := newData }
    if newSize.val = 0 then return ()
    let lenUsed := rangeLength usedSpan.1 usedSpan.2
    let newData ← if lenUsed.val = 0 then pure newData
      else lift (copyto newData (i 1) oldData usedSpan.1 lenUsed)
    let io ← get
    let newOffset := -getCompacted io - compacted
    set { io with data := newData, offset := newOffset, ptr := io.ptr - deleted, size := lenUsed }
  return ()

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
def source_truncate (n : Int) : M Unit := do
  let io ← get
  if !io.writable then throwArg "truncate failed, IOBuffer is not writeable"
  if !io.seekable then throwArg "truncate failed, IOBuffer is not seekable"
  if n < 0 then throwArg ("truncate failed, n bytes must be ≥ 0, got " ++ toString n)
  if n > io.maxsize.val then
    throwArg ("truncate failed, n bytes is exceeds IOBuffer maxsize " ++ toString io.maxsize.val)
  let n ← lift (toI n)
  let offset := getOffset io
  let currentSize := io.size - offset
  if io.reinit then
    let data ← lift (similarData io n)
    set { io with data := List.replicate data.length 0, reinit := false, size := n }
  else if n.val < currentSize.val then
    let io ← get
    let io := if (translateSeekPosition io io.mark).val > (n + offset).val
      then { io with mark := i (-1) } else io
    set { io with size := n + offset, ptr := imin io.ptr (n + offset + i 1) }
  else if n.val > currentSize.val then
    if (n + offset).val > io.maxsize.val then discard compact
    let io ← get
    resize (n + getOffset io) false
    let io ← get
    let hi := imin (i io.data.length) (n + getOffset io)
    let data ← lift (fillZero io.data (io.size + i 1) hi)
    set { io with data, size := hi }
  return ()

/--
Julia source: base/iobuffer.jl:597-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline ensureroom(io::GenericIOBuffer, nshort::Int) = ensureroom(io, UInt(nshort))
```
-/
def source_ensureroom_int (ensureRoomUInt : BufferState → U → M Unit) (io : BufferState) (nshort : I) : M Unit := do
  let n ← lift (toU nshort.val)
  ensureRoomUInt io n

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
def source_ensureroom (reallocate : U → M Unit) (slowpath : U → I → M Unit)
    (nshort : U) : M Unit := do
  let io ← get
  if !io.writable || io.reinit then reallocate nshort
  else
    let startOffset := if io.append then io.size else io.ptr - i 1
    let existingSpace := imin (i io.data.length - startOffset) (io.maxsize - (startOffset - getOffset io))
    if existingSpace.val < (JInt.rem .i64 nshort).val then slowpath nshort existingSpace
    else return ()

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
def source_ensureroom_reallocate (similar : BufferState → I → Except IOErr (List UInt8))
    (nshort : U) : M Unit := do
  let io ← get
  if !io.writable then throwArg "ensureroom failed, IOBuffer is not writeable"
  let data ← lift (similar io (imin io.maxsize (JInt.rem .i64 nshort)))
  set { io with data, reinit := false, offset := -getCompacted io }

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
def source_ensureroom_slowpath (nshort : U) (available : I) : M Unit := do
  let io ← get
  let (start, _) ← lift (getUsedSpan io)
  let reclaimable := start - i 1
  if reclaimable.val ≥ 32 && reclaimable.val ≥ (io.data.length / 8 : Nat) &&
      (JInt.rem .u64 (reclaimable + available)).val ≥ nshort.val then
    let _ ← compact
    return ()
  let n ← lift (toI nshort.val)
  let desiredSize := i io.data.length + n - available
  if desiredSize.val > io.maxsize.val then
    if reclaimable.val ≠ 0 then discard compact
    let io ← get
    if io.data.length < io.maxsize.val then resize io.maxsize true
  else resize desiredSize false
  return ()

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
def source_get_used_span (io : BufferState) : Except IOErr (I × I) :=
  if io.seekable then .ok (getOffset io + i 1, io.size)
  else if io.mark.val > -1 then .ok (imin io.ptr (translateSeekPosition io io.mark), io.size)
  else .ok (io.ptr, io.size)

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
def source_compact : M I := do
  let io ← get
  let offset := getOffset io
  let usedSpan ← lift (getUsedSpan io)
  let deleted := usedSpan.1 - i 1
  let compacted := deleted - offset
  if deleted.val = 0 then return i 0
  let data ← lift (copyto io.data (i 1) io.data (deleted + i 1) (rangeLength usedSpan.1 usedSpan.2))
  let newOffset := -getCompacted io - compacted
  set { io with data, offset := newOffset, ptr := io.ptr - deleted, size := io.size - deleted }
  return deleted

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
def source_close (resize : I → Bool → M Unit) : M Unit := do
  let io ← get
  if io.writable && !io.reinit then resize (i 0) true
  let newOffset := -getCompacted io
  modify fun io => { io with readable := false, writable := false, seekable := false, size := i 0, maxsize := i 0, ptr := i 1, mark := i (-1), offset := newOffset }

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
def source_take_generic (readInto : Nat → M (List UInt8)) : M (List UInt8) := do
  modify fun io => { io with mark := i (-1) }
  let io ← get
  let data ← if io.seekable then
    let offset := source_get_offset io
    let nbytes := io.size - offset
    let dest ← lift (source_StringVector stringNModel unsafeWrapModel wrapArrayModel nbytes.val)
    lift (copyto dest (i 1) io.data (offset + i 1) nbytes)
  else
    let nbytes := source_bytesavailable io
    let dest ← lift (source_StringVector stringNModel unsafeWrapModel wrapArrayModel nbytes.val)
    readInto dest.length
  let io ← get
  if io.writable then
    set { io with reinit := true, ptr := i 1, size := i 0, offset := i 0 }
  return data

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
def source_take_IOBuffer
    (wrapArray : List UInt8 → I → I → Except IOErr (List UInt8)) : M (List UInt8) := do
  modify fun io => { io with mark := i (-1) }
  let io ← get
  let data ← if io.seekable then
    let nbytes := source_filesize io
    if nbytes.val = 0 || io.reinit then
      lift (source_StringVector stringNModel unsafeWrapModel wrapArrayModel 0)
    else if io.writable then lift (wrapArray io.data (source_get_offset io + i 1) nbytes)
    else do
      let dest ← lift (source_StringVector stringNModel unsafeWrapModel wrapArrayModel nbytes.val)
      lift (copyto dest (i 1) io.data (source_get_offset io + i 1) nbytes)
  else
    let nbytes := source_bytesavailable io
    if nbytes.val = 0 then
      lift (source_StringVector stringNModel unsafeWrapModel wrapArrayModel 0)
    else if io.writable then lift (wrapArray io.data io.ptr nbytes)
    else throw (.errorException "Unreachable IOBuffer state")
  let io ← get
  if io.writable then set { io with reinit := true, ptr := i 1, size := i 0, offset := i 0 }
  return data

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
def source_unsafe_takestring (unsafeTake : List UInt8 → Nat → Except IOErr JuliaString)
    (unsafeCopy : List UInt8 → I → List UInt8 → I → I → Except IOErr (List UInt8))
    (unsafeTakeMemory : List UInt8 → Except IOErr JuliaString) : M JuliaString := do
  let io ← get
  let usedSpan ← lift (source_get_used_span io)
  let nbytes := rangeLength usedSpan.1 usedSpan.2
  let start := usedSpan.1
  if nbytes.val = 0 then return ⟨[]⟩
  if start.val = 1 then lift (unsafeTake io.data nbytes.val.toNat)
  else
    let memory ← lift (source_StringMemory stringNModel unsafeWrapModel (JInt.rem .u64 nbytes).val)
    let memory ← lift (unsafeCopy memory (i 1) io.data start nbytes)
    lift (unsafeTakeMemory memory)

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
def source_takestring_IOBuffer
    (unsafeTake : List UInt8 → Nat → Except IOErr JuliaString)
    (unsafeCopy : List UInt8 → I → List UInt8 → I → I → Except IOErr (List UInt8))
    (unsafeTakeMemory : List UInt8 → Except IOErr JuliaString) : M JuliaString := do
  let io ← get
  if io.reinit then return ⟨[]⟩
  if io.writable then
    let s ← source_unsafe_takestring unsafeTake unsafeCopy unsafeTakeMemory
    let io ← get
    set { io with reinit := true, mark := i (-1), ptr := i 1, size := i 0, offset := i 0 }
    return s
  else
    let usedSpan ← lift (source_get_used_span io)
    let nbytes := rangeLength usedSpan.1 usedSpan.2
    let memory ← lift (source_StringMemory stringNModel unsafeWrapModel nbytes.val)
    let memory ← lift (unsafeCopy memory (i 1) io.data usedSpan.1 nbytes)
    lift (unsafeTakeMemory memory)

/--
Julia source: base/iobuffer.jl:862-862 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
takestring!(io::GenericIOBuffer) = String(take!(io))
```
-/
def source_takestring_generic (readInto : Nat → M (List UInt8)) : M JuliaString := do
  let bytes ← source_take_generic readInto
  return ⟨bytes⟩

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
def source_unsafe_take (memoryref : List UInt8 → I → Except IOErr (List UInt8))
    (emptyMemoryref : Except IOErr (List UInt8))
    (wrapArray : List UInt8 → I → Except IOErr (List UInt8)) (io : BufferState) :
    Except IOErr (List UInt8) := do
  let offset := getOffset io
  let mem ← if io.size = offset then emptyMemoryref else memoryref io.data (offset + i 1)
  wrapArray mem (io.size - offset)

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
def source_write_buffer_to_IO {Out : Type} (same : Out → BufferState → Bool)
    (write : Out → List UInt8 → Except IOErr I) (to : Out) : M I := do
  let sourceBuf ← get
  if same to sourceBuf then throwArg "Writing all content fron an IOBuffer into itself in invalid"
  else
    if !sourceBuf.readable then throwNotReadable
    let bytes ← lift (pending sourceBuf)
    let written ← lift (write to bytes)
    modify fun sourceBuf => { sourceBuf with ptr := sourceBuf.size + i 1 }
    return written

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
def source_unsafe_write {P Cancel : Type}
    (precheckCancel : Cancel → Except IOErr Unit) (ensureroom : U → M Unit)
    (writePointer : List UInt8 → P → I → U → Except IOErr (List UInt8))
    (cancel : Cancel) (p : P) (nb : U) : M I := do
  let _ ← lift (precheckCancel cancel)
  ensureroom nb
  let buffer ← get
  let size := buffer.size
  let append := buffer.append
  let ptr := if append then size + i 1 else buffer.ptr
  let data := buffer.data
  let startOffset := ptr - i 1
  let available := imin (i data.length - startOffset)
    (buffer.maxsize - (startOffset - getOffset buffer))
  let availableUInt := JInt.rem .u64 available
  let toWriteUInt := uminU nb availableUInt
  let toWrite := imax (i 0) (JInt.rem .i64 toWriteUInt)
  let data ← lift (writePointer data p ptr (u toWrite.val))
  set { buffer with data := data }
  modify fun buffer => { buffer with size := imax size (startOffset + toWrite) }
  modify fun buffer => { buffer with ptr := if append then buffer.ptr else ptr + toWrite }
  return toWrite

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
def source_unsafe_write_vector {Data P : Type}
    (setIndex : Data → Int → UInt8 → Except IOErr Data)
    (loadPointer : P → Except IOErr UInt8) (advancePointer : P → P)
    (data : Data) (p : P) (start : Int) (nb : U) : Except IOErr (Data × P) := do
  let mut data := data
  let mut p := p
  for i in List.range nb.val.toNat do
    let byte ← loadPointer p
    data ← setIndex data (start + i) byte
    p := advancePointer p
  pure (data, p)

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
def source_unsafe_write_dense {Data P : Type}
    (setIndex : Data → Int → UInt8 → Except IOErr Data)
    (loadPointerAt : P → U → Except IOErr UInt8)
    (pointer : Data → Int → P) (unsafeCopy : P → P → U → Except IOErr Unit)
    (data : Data) (p : P) (start : Int) (nb : U) : Except IOErr Data := do
  if nb.val < 5 then
    let mut data := data
    for k in List.range nb.val.toNat do
      let i := u (k + 1)
      let byte ← loadPointerAt p i
      data ← setIndex data (start + (i.val) - 1) byte
    pure data
  else
    let dest := pointer data start
    let _ ← unsafeCopy dest p nb
    pure data

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
def source_write_uint8 (ensureRoom : U → M Unit) (setByte : BufferState → I → UInt8 → Except IOErr (List UInt8))
    (a : UInt8) : M I := do
  ensureRoom (u 1)
  let to ← get
  let ptr := if to.append then to.size + i 1 else to.ptr
  if (ptr - getOffset to).val > to.maxsize.val then return i 0
  let data ← lift (setByte to ptr a)
  let size := imax to.size ptr
  let ptr := if to.append then to.ptr else to.ptr + i 1
  set { to with data, size, ptr }
  return i 1


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
def source_readbytes_int {B P : Type} (length : B → Int)
    (resize : B → Int → Except IOErr B) (checkBounds : B → I → Except IOErr Unit)
    (pointer : B → P) (unsafeRead : BufferState → P → U → M Unit) (b : B) (nb : I) : M I := do
  let io ← get
  if !io.readable then throwNotReadable
  let toRead := imin nb (bytesavailable io)
  let b ← if length b < toRead.val then lift (resize b toRead.val) else pure b
  let _ ← lift (checkBounds b toRead)
  unsafeRead io (pointer b) (u toRead.val)
  return toRead
/--
Julia source: base/iobuffer.jl:965-965 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readbytes!(io::GenericIOBuffer, b::MutableDenseArrayType{UInt8}, nb=length(b)) = readbytes!(io, b, Int(nb)::Int)
```
-/
def source_readbytes_default {B P N : Type} (length : B → Int) (defaultValue : Int → N)
    (toInt : N → Except IOErr I) (resize : B → Int → Except IOErr B)
    (checkBounds : B → I → Except IOErr Unit) (pointer : B → P)
    (unsafeRead : BufferState → P → U → M Unit) (b : B) (nb : Option N) : M I := do
  let count ← lift (toInt (nb.getD (defaultValue (length b))))
  source_readbytes_int length resize checkBounds pointer unsafeRead b count

/--
Julia source: base/iobuffer.jl:977-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::GenericIOBuffer) = read!(io, StringVector(bytesavailable(io)))
```
-/
def source_read_all (readInto : Nat → M (List UInt8)) : M (List UInt8) := do
  let io ← get
  let data ← lift (source_StringVector stringNModel unsafeWrapModel wrapArrayModel
    (bytesavailable io).val)
  readInto data.length

/--
Julia source: base/iobuffer.jl:980-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readavailable(io::GenericIOBuffer) = read(io)
```
-/
def source_readavailable (readInto : Nat → M (List UInt8)) : M (List UInt8) :=
  source_read_all readInto

/--
Julia source: base/iobuffer.jl:982-982 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
read(io::GenericIOBuffer, nb::Integer) = read!(io, StringVector(min(nb, bytesavailable(io))))
```
-/
def source_read_n (readInto : Nat → M (List UInt8)) (nb : Int) : M (List UInt8) := do
  let io ← get
  let n := min nb (bytesavailable io).val
  let data ← lift (source_StringVector stringNModel unsafeWrapModel wrapArrayModel n)
  readInto data.length

/--
Julia source: base/iobuffer.jl:984-986 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function occursin(delim::UInt8, buf::GenericIOBuffer)
    return in(delim, view(buf.data, buf.ptr:buf.size))
end
```
-/
def source_occursin (delim : UInt8) (buf : BufferState) : Except IOErr Bool := do
  let data ← pending buf
  pure (data.contains delim)

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
def source_copyuntil {Out Cancel : Type} [BEq Cancel]
    (writeDefault : Out → List UInt8 → Except IOErr Out)
    (writeCancel : Out → List UInt8 → Cancel → Except IOErr Out)
    (cancel : Cancel) (defaultCancel : Cancel) (out : Out) (io : BufferState)
    (delim : UInt8) (keep : Bool) : Except IOErr (Out × BufferState) := do
  let data ← pending io
  let nread := findOrLen data delim
  let nout := if !keep && nread > 0 && data[nread - 1]! = delim then nread - 1 else nread
  let bytes := data.take nout
  let out ← if cancel == defaultCancel then writeDefault out bytes else writeCancel out bytes cancel
  let io := { io with ptr := io.ptr + i nread }
  pure (out, io)

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
def source_copyline_buffer {Stream Cancel : Type} [BEq Cancel]
    (checkCancel : Cancel → Except IOErr Cancel)
    (copyUntilDefault : BufferState → Stream → UInt8 → Bool → Except IOErr BufferState)
    (copyUntilToken : BufferState → Stream → UInt8 → Bool → Cancel → Except IOErr BufferState)
    (write : BufferState → List UInt8 → Cancel → Except IOErr BufferState)
    (cancel defaultCancel : Cancel) (out : BufferState) (stream : Stream) (keep : Bool) :
    Except IOErr BufferState := do
  let tok ← checkCancel cancel
  if !out.append && out.ptr.val < (out.size + i 1).val then
    let newbuf ← source_IOBuffer_empty (some true) (some true) none (some true) (2 ^ 63 - 1) none
    let newbuf ← if cancel == defaultCancel then copyUntilDefault newbuf stream 0x0a true
      else copyUntilToken newbuf stream 0x0a true tok
    let v ← match (source_take_IOBuffer wrapBytes).run newbuf with
      | .ok bytes _ => .ok bytes
      | .error e _ => .error e
    let v := if !keep && v.length > 1 && v.getLast? = some 0x0a then v.dropLast else v
    let v := if !keep && v.length > 1 && v.getLast? = some 0x0d then v.dropLast else v
    write out v tok
  else
    let out ← if cancel == defaultCancel then copyUntilDefault out stream 0x0a true
      else copyUntilToken out stream 0x0a true tok
    let idx := out.size
    if keep || idx = out.offset then return out
    let last ← getChecked out.data idx
    if last != 0x0a then return out
    let idx ← if idx.val < 2 then pure (idx - i 1) else do
      let previous ← getChecked out.data (idx - i 1)
      pure (if previous = 0x0d then idx - i 2 else idx - i 1)
    pure { out with size := idx, ptr := if out.append then out.ptr else idx + i 1 }

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
def source_copyline_read {Out Cancel : Type} [BEq Cancel]
    (writeDefault : Out → List UInt8 → Except IOErr Out)
    (writeCancel : Out → List UInt8 → Cancel → Except IOErr Out)
    (cancel : Cancel) (defaultCancel : Cancel) (out : Out) (io : BufferState)
    (keep : Bool) : Except IOErr (Out × BufferState) := do
  let data ← pending io
  let nread := findOrLen data 0x0a
  let nout := if !keep && nread > 0 && data[nread - 1]! = 0x0a then
      if nread - 1 > 0 && data[nread - 2]! = 0x0d then nread - 2 else nread - 1
    else nread
  let bytes := data.take nout
  let out ← if cancel == defaultCancel then writeDefault out bytes else writeCancel out bytes cancel
  pure (out, { io with ptr := io.ptr + i nread })

/--
Julia source: base/iobuffer.jl:1079-1079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyline(out::IO, io::GenericIOBuffer; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL) = _copyline(out, io; keep, cancel)
```
-/
def source_copyline_IO {Out Cancel : Type} [BEq Cancel]
    (writeDefault : Out → List UInt8 → Except IOErr Out)
    (writeCancel : Out → List UInt8 → Cancel → Except IOErr Out)
    (cancel defaultCancel : Cancel) (out : Out) (io : BufferState) (keep : Bool) :
    Except IOErr (Out × BufferState) :=
  source_copyline_read writeDefault writeCancel cancel defaultCancel out io keep

/--
Julia source: base/iobuffer.jl:1080-1080 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyline(out::GenericIOBuffer, io::GenericIOBuffer; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL) = _copyline(out, io; keep, cancel)
```
-/
def source_copyline_buffer_buffer {Cancel : Type} [BEq Cancel]
    (writeDefault : BufferState → List UInt8 → Except IOErr BufferState)
    (writeCancel : BufferState → List UInt8 → Cancel → Except IOErr BufferState)
    (cancel defaultCancel : Cancel) (out io : BufferState) (keep : Bool) :
    Except IOErr (BufferState × BufferState) :=
  source_copyline_read writeDefault writeCancel cancel defaultCancel out io keep

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
def source_crc32c_bytes {P : Type} (unsafeCRC : P → I → UInt32 → Except IOErr UInt32)
    (pointer : BufferState → I → P) (nb : Int) (crc : Option UInt32) : M UInt32 := do
  if nb < 0 then throwArg ("number of bytes to checksum must be ≥ 0, got " ++ toString nb)
  let io ← get
  if !io.readable then lift source_throw_not_readable
  let n ← lift (toI (min nb (source_bytesavailable io).val))
  let crc := crc.getD 0x00000000
  if n.val = 0 then return crc
  let crc ← lift (unsafeCRC (pointer io io.ptr) n crc)
  modify fun io => { io with ptr := io.ptr + n }
  return crc

/--
Julia source: base/iobuffer.jl:1093-1093 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(io::IOBuffer, crc::UInt32=0x00000000) = _crc32c(io, bytesavailable(io), crc)
```
-/
def source_crc32c_default {P : Type}
    (unsafeCRC : P → I → UInt32 → Except IOErr UInt32)
    (pointer : BufferState → I → P) (crc : Option UInt32) : M UInt32 := do
  let io ← get
  source_crc32c_bytes unsafeCRC pointer (source_bytesavailable io).val crc


/-! ## Concrete list-backed instantiations used by specifications -/

def ensureRoomModel (nshort : U) : M Unit :=
  source_ensureroom
    (fun n => source_ensureroom_reallocate (fun io len => similarData io len) n)
    source_ensureroom_slowpath nshort

def copyModel (similar : List UInt8 → I → Except IOErr (List UInt8)) (b : BufferState) :
    Except IOErr BufferState :=
  source_copy
    (fun buffer count =>
      if buffer.isMemory then
        source_similar_data_IOBuffer (source_StringMemory stringNModel unsafeWrapModel) buffer count
      else source_similar_data_generic similar buffer count)
    (fun bytes readable writable seekable append maxsize truncate =>
      source_GenericIOBuffer (if b.isMemory then .mem bytes else .other bytes)
        readable writable seekable append maxsize.val truncate) b

def peekArrayModel {T : Type} (isFloat : Bool) (uintZero unsignedZero : T)
    (sizeOf : T → Nat) (convertByte : UInt8 → T) (shift : T → Nat → T)
    (bitOr : T → T → T) (ltoh reinterpret : T → T) (typeValue : T) : M T :=
  source_peek_multibyte sizeOf
    (fun io _ => .ok (source_load_from_array isFloat uintZero unsignedZero sizeOf
      (fun bytes index => bytes.getD (index - 1).toNat 0)
      convertByte shift bitOr ltoh reinterpret io.data io.ptr)) typeValue

def loadUIntModel (io : BufferState) (_typeValue : U) : Except IOErr U :=
  .ok (source_load_from_array false (u 0) (u 0) (fun _ => 8)
    (fun bytes index => bytes.getD (index - 1).toNat 0)
    (fun byte => u byte.toNat) (fun word shift => u (word.val * 2 ^ shift))
    (fun a b => u (Nat.lor a.val.toNat b.val.toNat)) id id io.data io.ptr)

def readUIntModel : M U :=
  source_read_multibyte (source_peek_multibyte (fun _ => 8) loadUIntModel)
    (fun _ => 8) (u 0)

def writePointerModel (data source : List UInt8) (start : I) (count : U) : Except IOErr (List UInt8) :=
  match source_unsafe_write_vector
      (fun bytes index byte => setChecked bytes (i index) byte)
      (fun (bytes, offset) =>
        match bytes[offset]? with
        | some byte => .ok byte
        | none => .error .outOfBounds)
      (fun (bytes, offset) => (bytes, offset + 1))
      data (source, 0) start.val count with
  | .ok (updated, _) => .ok updated
  | .error error => .error error

def writeBytesModel (bytes : List UInt8) : M I :=
  source_unsafe_write (fun _ => .ok ()) ensureRoomModel writePointerModel () bytes (u bytes.length)

def writeByteModel (byte : UInt8) : M I :=
  source_write_uint8 ensureRoomModel (fun io ptr b => setChecked io.data ptr b) byte

def readAllModel : M (List UInt8) :=
  source_read_all (fun n => readBang n)

def unsafeTakeModel (data : List UInt8) (n : Nat) : Except IOErr JuliaString :=
  .ok ⟨data.take n⟩

def unsafeTakeMemoryModel (data : List UInt8) : Except IOErr JuliaString :=
  .ok ⟨data⟩

end JuliaLean.base.iobuffer
