import JuliaLean.Core

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
