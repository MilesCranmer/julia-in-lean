import JuliaLean.IOCov.Common

set_option linter.unusedSimpArgs false

/-!
Models of the generic `IO` methods of `base/io.jl` at master `bbfa0ce4150`.

A generic stream is a `St`: the bytes already consumed (`pre`), the unread bytes
(`inp`), the `mark` field (`-1` when unmarked), the bytes written (`out`), whether
the concrete type supports `seek`, and whether it is open. The methods that each
`IO` subtype must define (`read(s, UInt8)`, `write(s, ::UInt8)`, `eof`, `seek`,
`close`, ...) are the primitive operations on `St`; the generic methods of
`io.jl` are modelled on top of them, mirroring their loops.
-/

namespace JuliaLean.IOCov.Io

open JuliaLean JuliaLean.IOCov

abbrev Bytes := List UInt8

structure St where
  pre : Bytes
  inp : Bytes
  mark : Int := -1
  out : Bytes := []
  seekable : Bool := true
  isopen : Bool := true
  deriving DecidableEq, Repr

/-- A stream whose unread contents are `b`. -/
def St.of (b : Bytes) : St := { pre := [], inp := b }

/-! ## Primitive operations of a concrete stream type -/

/-- `eof(s)`. -/
def eof (s : St) : Bool := s.inp.isEmpty
/-- `read(s, UInt8)` of a concrete type: `EOFError` at the end. -/
def readByte (s : St) : R (UInt8 × St) :=
  match s.inp with
  | [] => .error .eofError
  | b :: r => .ok (b, { s with pre := s.pre ++ [b], inp := r })
/-- `write(s, b::UInt8)` of a concrete type: appends `b`, returns 1. -/
def writeByte (s : St) (b : UInt8) : Nat × St := (1, { s with out := s.out ++ [b] })
/-- `position(s)`. -/
def position (s : St) : Nat := s.pre.length
/-- `seek(s, n)` of a concrete type (as for `IOBuffer`: allowed when seekable, or when
`n` is the mark of a marked stream). -/
def seek (s : St) (n : Nat) : R St :=
  if s.seekable || (s.mark ≥ 0 && (n : Int) = s.mark) then
    let all := s.pre ++ s.inp
    .ok { s with pre := all.take n, inp := all.drop n }
  else argErr "seek failed, IOBuffer is not seekable and is not marked"
/-- `skip(s, n) = seek(s, position(s) + n)`. -/
def skip (s : St) (n : Int) : R St := seek s ((position s : Int) + n).toNat
/-- `close(s)`. -/
def close (s : St) : St := { s with isopen := false }

/-! ## Exceptions and trivial methods, lines 25-48 -/

/-- `struct SystemError`, lines 25-31: `prefix`, `errnum`, `extrainfo`. -/
structure SystemErrorM where
  pfx : String
  errnum : Int
  extrainfo : Option String
  deriving DecidableEq, Repr

/-- `SystemError(p, e, extrainfo)`, line 28 (`errnum::Int32` converts `e`). -/
def systemError3 (p : String) (e : Int) (x : Option String) : R SystemErrorM := do
  let e ← toInt .i32 e
  pure ⟨p, e, x⟩
/-- `SystemError(p, e)`, line 29. -/
def systemError2 (p : String) (e : Int) : R SystemErrorM := systemError3 p e none
/-- `SystemError(p) = new(p, Libc.errno(), nothing)`, line 30. -/
def systemError1 (errno : Int) (p : String) : R SystemErrorM := systemError3 p errno none

/-- `lock(::IO) = nothing`, `unlock(::IO) = nothing`, `reseteof(x::IO) = nothing`. -/
def lockIO (_s : St) : Unit := ()
def unlockIO (_s : St) : Unit := ()
def reseteof (_s : St) : Unit := ()
/-- `buffer_writes(x::IO, bufsize=SZ_UNBUFFERED_IO) = x`, line 48. -/
def bufferWrites (s : St) (_bufsize : Nat := 65536) : St := s
/-- `isreadable(io::IO) = isopen(io)`, line 124; `iswritable(io::IO) = isopen(io)`, line 147. -/
def isreadable (s : St) : Bool := s.isopen
def iswritable (s : St) : Bool := s.isopen
/-- `isreadonly(s) = isreadable(s) && !iswritable(s)`, line 893. -/
def isreadonly (r w : Bool) : Bool := r && !w
/-- `flush(io::IO) = nothing`, line 1620. -/
def flushIO (_s : St) : Unit := ()

/-- `read(stream, ::Type{Union{}}, slurp...)`, line 263. -/
def readUnion {α} (_s : St) : R α := .error (.errorException "cannot read a value of type Union{}")
/-- `peek(s::IO, ::Type{Union{}}, slurp...)`, line 389. -/
def peekUnion {α} (_s : St) : R α := .error (.methodError "peek")
/-- `read(s::IO, ::Type{UInt8})` and `write(s::IO, x::UInt8)` fallbacks, lines 346-347: a type
without byte I/O. -/
def readByteFallback {α} (tyname : String) : R α := .error (.errorException (tyname ++ " does not support byte I/O"))
/-- `write(io::IO, x) = throw(MethodError(write, (io, x)))`, line 897. -/
def writeFallback {α} : R α := .error (.methodError "write")
/-- `read(s::IO, T::Type)`, line 1345. -/
def readTypeFallback {α} (tname : String) : R α :=
  .error (.errorException ("The IO stream does not support reading objects of type " ++ tname ++ "."))

/-! ## Byte loops, lines 343-391 -/

/-- `writepartial(io::IO, x) = write(io, x)`, line 343. -/
def writepartial {α} (write : St → α) (s : St) : α := write s

/-- `unsafe_write(s::IO, p::Ptr{UInt8}, n::UInt)`, lines 358-364: one `write(s, byte)` per
byte, summing the counts. -/
def unsafeWrite (s : St) : Bytes → Nat × St
  | [] => (0, s)
  | b :: bs =>
    let (k, s1) := writeByte s b
    let (n, s2) := unsafeWrite s1 bs
    (k + n, s2)

/-- `unsafe_read(s::IO, p::Ptr{UInt8}, n::UInt)`, lines 375-380: `n` calls of
`read(s, UInt8)`; the stored bytes are returned. -/
def unsafeRead : Nat → St → R (Bytes × St)
  | 0, s => .ok ([], s)
  | n + 1, s => do
    let (b, s1) ← readByte s
    let (bs, s2) ← unsafeRead n s1
    pure (b :: bs, s2)

/-- `mark(io::IO)`, lines 1575-1577. -/
def mark (s : St) : Int × St := (position s, { s with mark := position s })
/-- `ismarked(io::IO) = io.mark >= 0`, line 1615. -/
def ismarked (s : St) : Bool := decide (s.mark ≥ 0)
/-- `unmark(io::IO)`, lines 1586-1590. -/
def unmark (s : St) : Bool × St := if !ismarked s then (false, s) else (true, { s with mark := -1 })
/-- `reset(io::T)`, lines 1600-1606. -/
def reset (s : St) : R (Int × St) :=
  if !ismarked s then argErr "not marked" else do
    let m := s.mark
    let s1 ← seek s m.toNat
    pure (m, { s1 with mark := -1 })

/-- `peek(s::IO, ::Type{T})`, lines 382-388: `mark`, `read(s, T)`, and `reset` in `finally`.
`read` is the reader of `T`. -/
def peek {α} (read : St → R (α × St)) (s : St) : R (α × St) :=
  let s1 := (mark s).2
  match read s1 with
  | .ok (v, s2) => do let (_, s3) ← reset s2; pure (v, s3)
  | .error e => match reset s1 with
    | .ok _ => .error e
    | .error e' => .error e'
/-- `peek(s) = peek(s, UInt8)::UInt8`, line 391. -/
def peekByte (s : St) : R (UInt8 × St) := peek readByte s

/-! ## `open_flags` and `open(f, args...)`, lines 401-456 -/

structure Flags where
  read : Bool
  write : Bool
  create : Bool
  truncate : Bool
  append : Bool
  deriving DecidableEq, Repr

/-- `open_flags(; read, write, create, truncate, append)`, lines 401-431; `none` is `nothing`. -/
def openFlags (read write create truncate append : Option Bool) : Flags :=
  let (create, truncate) :=
    if write = some true ∧ read ≠ some true ∧ append ≠ some true then
      (if create = none then some true else create, if truncate = none then some true else truncate)
    else (create, truncate)
  let (write, create) :=
    if truncate = some true ∨ append = some true then
      (if write = none then some true else write, if create = none then some true else create)
    else (write, create)
  let write := write.getD false
  let read := read.getD (!write)
  ⟨read, write, create.getD false, truncate.getD false, append.getD false⟩

/-- `open(f::Function, args...; kwargs...)`, lines 449-456: `f` runs on the opened stream
and the stream it leaves is closed whether or not `f` throws. `f` returns its result and
the stream state. -/
def openDo {α} (opened : R St) (f : St → R α × St) : R α × Option St :=
  match opened with
  | .error e => (.error e, none)
  | .ok io => let (r, io') := f io; (r, some (close io'))

/-! ## `AbstractPipe`, lines 476-542 -/

/-- A pipe object: its reader and writer streams (`pipe_reader`, `pipe_writer`). -/
structure Pipe where
  rd : St
  wr : St
  deriving DecidableEq, Repr

/-- `pipe_reader(io)`, `pipe_writer(io)`, lines 486-487. -/
def pipeReader (p : Pipe) : St := p.rd
def pipeWriter (p : Pipe) : St := p.wr
/-- Run a reader operation on `pipe_reader(io)`. -/
def onReader {α} (op : St → R (α × St)) (p : Pipe) : R (α × Pipe) := do
  let (a, s) ← op (pipeReader p)
  pure (a, { p with rd := s })
/-- Run a writer operation on `pipe_writer(io)`. -/
def onWriter {α} (op : St → R (α × St)) (p : Pipe) : R (α × Pipe) := do
  let (a, s) ← op (pipeWriter p)
  pure (a, { p with wr := s })

/-- `getproperty(pipe::AbstractPipe, name)`, lines 478-484: the stream fields are
type-asserted to be `IO`. -/
def pipeGetproperty {α} (getfield : String → α) (isIO : α → Bool) (name : String) : R α :=
  if name ∈ ["in", "in_stream", "out", "out_stream", "err", "err_stream"] then
    if isIO (getfield name) then .ok (getfield name) else .error (.typeError "typeassert")
  else .ok (getfield name)

/-- `iswritable(io::AbstractPipe)`, line 489. -/
def pipeIswritable (p : Pipe) : Bool := iswritable (pipeWriter p)
/-- `flush`/`closewrite(io::AbstractPipe)`, lines 496-498 (the `@eval` loop). -/
def pipeFlushLike (f : St → R (Unit × St)) (p : Pipe) : R (Unit × Pipe) := onWriter f p
/-- `write(io::AbstractPipe, byte::UInt8)`, line 500. -/
def pipeWriteByte (p : Pipe) (b : UInt8) : R (Nat × Pipe) := onWriter (fun s => .ok (writeByte s b)) p
/-- `writepartial(io::AbstractPipe, x)`, line 501. -/
def pipeWritepartial {α} (w : St → R (α × St)) (p : Pipe) : R (α × Pipe) := onWriter (writepartial w) p
/-- `write(to::IO, from::AbstractPipe) = write(to, pipe_reader(from))`, line 502. -/
def writeFromPipe {α} (w : St → St → α) (to : St) (p : Pipe) : α := w to (pipeReader p)
/-- `unsafe_write(io::AbstractPipe, p, nb)`, lines 503-505. -/
def pipeUnsafeWrite (p : Pipe) (bs : Bytes) : R (Nat × Pipe) := onWriter (fun s => .ok (unsafeWrite s bs)) p
/-- `buffer_writes(io::AbstractPipe, args...)`, line 506. -/
def pipeBufferWrites (p : Pipe) : St := bufferWrites (pipeWriter p)
/-- `mark`, `unmark`, `reset`, `ismarked`, `read`, `bytesavailable`, `reseteof`, `isreadable`
on `AbstractPipe`, line 513 (the `@eval` loop): forwarded to `pipe_reader`. -/
def pipeReaderOp {α} (f : St → R (α × St)) (p : Pipe) : R (α × Pipe) := onReader f p
/-- `readavailable(io::AbstractPipe)`, lines 517-519. -/
def pipeReadavailable (ra : St → R (Bytes × St)) (p : Pipe) : R (Bytes × Pipe) := onReader ra p
/-- `read(io::AbstractPipe, ::Type{UInt8})`, lines 520-522. -/
def pipeReadByte (p : Pipe) : R (UInt8 × Pipe) := onReader readByte p
/-- `unsafe_read(io::AbstractPipe, p, nb)`, line 523. -/
def pipeUnsafeRead (p : Pipe) (n : Nat) : R (Bytes × Pipe) := onReader (unsafeRead n) p
/-- `copyuntil(out, io::AbstractPipe, arg)` for `UInt8`, `AbstractChar`, `AbstractString`,
`AbstractVector` delimiters, lines 524-527, and `readuntil_vector!(io::AbstractPipe, ...)`,
line 528, and `readbytes!(io::AbstractPipe, ...)`, lines 531-533, and
`peek(io::AbstractPipe, T)`, line 534, and `wait_readnb(io::AbstractPipe, nb)`, line 535:
forwarded with the same arguments to `pipe_reader(io)`. -/
def pipeForward {α} (op : St → R (α × St)) (p : Pipe) : R (α × Pipe) := onReader op p
/-- `eof(io::AbstractPipe)`, lines 536-538. -/
def pipeEof (p : Pipe) : Bool := eof (pipeReader p)
/-- `isopen(io::AbstractPipe)`, line 540. -/
def pipeIsopen (p : Pipe) : Bool := (pipeWriter p).isopen || (pipeReader p).isopen
/-- `close(io::AbstractPipe)`, line 541: writer first, then reader. -/
def pipeClose (p : Pipe) : Pipe := let p1 := { p with wr := close (pipeWriter p) }; { p1 with rd := close (pipeReader p1) }
/-- `wait_close(io::AbstractPipe)`, line 542: writer, then reader. -/
def pipeWaitClose (wc : St → List String) (p : Pipe) : List String := wc (pipeWriter p) ++ wc (pipeReader p)

/-! ## Binary I/O, lines 897-1037 -/

/-- The `n` little-endian bytes of `x` (the memory of `Ref(x)` on the supported
little-endian platforms). -/
def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, x => (x % 256).toUInt8 :: leBytes n (x / 256)

/-- The value of little-endian bytes. -/
def leVal : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leVal bs

/-- The two's-complement bit pattern of `x : T`. -/
def bitsOf (t : IntTy) (x : Int) : Nat := (x % 2 ^ t.bits).toNat

/-- `write(io::IO, x1, xs...)`, lines 898-905: `write` each argument, summing counts. -/
def writeMany {α} (w : St → α → Nat × St) (s : St) (x1 : α) (xs : List α) : Nat × St :=
  let (n, s1) := w s x1
  xs.foldl (fun (acc : Nat × St) x => let (k, s') := w acc.2 x; (acc.1 + k, s')) (n, s1)

/-- `unsafe_write(s, p::Ref{T}, n)` and `unsafe_write(s, p::Ptr, n)`, lines 907-909: convert
the pointer and the count, then the byte method. -/
def unsafeWriteRef (s : St) (mem : Bytes) (n : Int) : R (Nat × St) := do
  let n ← toInt .u64 n
  pure (unsafeWrite s (mem.take n.toNat))
/-- `write(s::IO, x::Ref{T})`, lines 910-917: `isbits` contents are written as their
`sizeof(T)` bytes, otherwise `write(s, x[])`. -/
def writeRef (isPtr isbits : Bool) (bytes : Bytes) (writeVal : St → R (Nat × St)) (s : St) :
    R (Nat × St) :=
  if isPtr then .error (.errorException "write cannot copy from a Ptr")
  else if isbits then .ok (unsafeWrite s bytes) else writeVal s
/-- `write(s::IO, x::Int8) = write(s, reinterpret(UInt8, x))`, line 918. -/
def writeInt8 (s : St) (x : Int) : Nat × St := writeByte s (bitsOf .i8 x).toUInt8
/-- `write(s::IO, x::Union{Int16,...,Float64})`, lines 919-921: `unsafe_write(s, Ref(x),
sizeof(x))`; a float is its bit pattern `bits` of `nbytes` bytes. -/
def writeInt (t : IntTy) (s : St) (x : Int) : Nat × St := unsafeWrite s (leBytes (t.bits / 8) (bitsOf t x))
def writeFloat (nbytes : Nat) (s : St) (bits : Nat) : Nat × St := unsafeWrite s (leBytes nbytes bits)
/-- `write(s::IO, x::Bool) = write(s, UInt8(x))`, line 923. -/
def writeBool (s : St) (b : Bool) : Nat × St := writeByte s (if b then 1 else 0)
/-- `write(to::IO, p::Ptr) = write(to, convert(UInt, p))`, line 924. -/
def writePtr (s : St) (p : Nat) : Nat × St := writeInt .u64 s p

/-- `write(s::IO, A::AbstractArray)`, lines 926-938: each element through a `Ref`;
elements are given by their bytes. -/
def writeArray (isbits : Bool) (s : St) (elems : List Bytes) : R (Nat × St) :=
  if !isbits then .error (.errorException "`write` is not supported on non-isbits arrays")
  else .ok (elems.foldl (fun (acc : Nat × St) e => let (k, s') := unsafeWrite acc.2 e; (acc.1 + k, s')) (0, s))

/-- `merge_adjacent_dim(sz, st)` (`base/reshapedarray.jl:448-465`) on the dimensions
`sz`, `st` from `n` on; returns `(msz, mst, n)`. -/
def mergeLoop (sz st : List Nat) : Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, m, s, n => (m, s, n)
  | fuel + 1, m, s, n =>
    if n < sz.length then
      let szn := sz.getD n 0
      let stn := st.getD n 0
      if m = 1 then mergeLoop sz st fuel szn stn (n + 1)
      else if stn = s * m ∨ szn = 1 then mergeLoop sz st fuel (m * szn) s (n + 1)
      else (m, s, n)
    else (m, s, n)
def mergeAdjacentDim (sz st : List Nat) : Nat × Nat × Nat :=
  match sz, st with
  | [], _ => (1, 1, 0)
  | [a], [b] => (a, b, 1)
  | a :: _, b :: _ => mergeLoop sz st sz.length a b 1
  | _, _ => (1, 1, 0)

/-- Column-major `CartesianIndices(dims)`, as lists of 1-based indices. -/
def cartesian : List Nat → List (List Nat)
  | [] => [[]]
  | d :: ds => (cartesian ds).flatMap (fun J => (List.range d).map (fun i => (i + 1) :: J))

/-- How a strided array write/read is carried out by `write(s, A::StridedArray)`,
lines 940-971, and `read!(s, A::StridedArray)`, lines 1059-1089. -/
inductive StridedPlan where
  | notIsbits
  | whole (nelem : Nat)
  | generic
  | runs (offsets : List Nat) (msz : Nat)
  deriving DecidableEq, Repr

/-- The dispatch and the run offsets (in elements, from `pointer(A)`) of the strided
methods: contiguous arrays are one `unsafe_write`; `mst != 1` falls back to the
`AbstractArray` method; otherwise one run of `msz` elements per index of the
remaining dimensions `sz′` padded with ones, at offset `sum(st′[i]*(I[i]-1))`. -/
def stridedPlan (isbits contiguous : Bool) (sz st : List Nat) : StridedPlan :=
  if !isbits then .notIsbits
  else if contiguous then .whole (sz.foldl (· * ·) 1)
  else
    let (msz, mst, n) := mergeAdjacentDim sz st
    if mst ≠ 1 then .generic
    else if n = sz.length then .whole (sz.foldl (· * ·) 1)
    else
      -- `sz′, st′ = tail(sz), tail(st)`; `n - 1` shifts `(tail(x)..., pad)`
      let shift (l : List Nat) (pad : Nat) (k : Nat) : List Nat :=
        (List.range k).foldl (fun acc _ => acc.tail ++ [pad]) l
      let sz' := shift sz.tail 1 (n - 1)
      let st' := shift st.tail 0 (n - 1)
      let offs := (cartesian sz').map (fun I =>
        ((List.range sz'.length).map (fun i => st'.getD i 0 * (I.getD i 1 - 1))).foldl (· + ·) 0)
      .runs offs msz

/-- `write(s::IO, A::StridedArray)`: the elements are read from memory `mem` (element
`k` at `mem[k]`, 0-based from `pointer(A)`); `generic` gives the `AbstractArray` method's
column-major element list. -/
def writeStrided (isbits contiguous : Bool) (sz st : List Nat) (mem : List Bytes)
    (genericElems : List Bytes) (s : St) : R (Nat × St) :=
  match stridedPlan isbits contiguous sz st with
  | .notIsbits => .error (.errorException "`write` is not supported on non-isbits arrays")
  | .whole n => .ok (unsafeWrite s (mem.take n).flatten)
  | .generic => writeArray true s genericElems
  | .runs offs msz => .ok (offs.foldl (fun (acc : Nat × St) o =>
      let (k, s') := unsafeWrite acc.2 ((mem.drop o).take msz).flatten; (acc.1 + k, s')) (0, s))

/-- `read!(s::IO, A::StridedArray{T})`, lines 1059-1089: non-`isbits` or contiguous arrays
use the `AbstractArray` method; otherwise as for `write`, with `unsafe_read` of runs.
The result lists the `(offset, bytes)` stores into the array memory (offsets in elements,
`nb` bytes per element); `generic` stands for the `AbstractArray` method. -/
def readStrided (isbits contiguous : Bool) (sz st : List Nat) (nb : Nat) (s : St) :
    R (Option (List (Nat × Bytes)) × St) :=
  if !isbits || contiguous then .ok (none, s)
  else
    match stridedPlan true false sz st with
    | .whole n => do let (bs, s') ← unsafeRead (nb * n) s; pure (some [(0, bs)], s')
    | .runs offs msz =>
      let rec go : List Nat → St → R (List (Nat × Bytes) × St)
        | [], s => .ok ([], s)
        | o :: os, s => do
          let (bs, s1) ← unsafeRead (nb * msz) s
          let (rest, s2) ← go os s1
          pure ((o, bs) :: rest, s2)
      do let (ws, s') ← go offs s; pure (some ws, s')
    | _ => .ok (none, s)

/-- `write(io::IO, c::Char)`, lines 973-980: the bytes of `bswap(reinterpret(UInt32, c))`
from the least significant, stopping once the rest is zero (at least one byte). -/
def writeCharLoop (s : St) (u : Nat) (n : Nat) : Nat × St :=
  let (k, s1) := writeByte s (u % 256).toUInt8
  if u / 256 = 0 then (n + k, s1) else writeCharLoop s1 (u / 256) (n + k)
termination_by u
decreasing_by omega

/-- `bswap` of a `UInt32`. -/
def bswap32 (c : Nat) : Nat :=
  (c % 256) * 2 ^ 24 + (c / 256 % 256) * 2 ^ 16 + (c / 65536 % 256) * 2 ^ 8 + c / 16777216 % 256
def writeChar (s : St) (c : Nat) : Nat × St := writeCharLoop s (bswap32 c) 0

/-- `write(io::IO, s::Symbol)`, lines 984-987: `unsafe_write` of the `strlen` bytes of the
name. -/
def writeSymbol (s : St) (name : Bytes) : Nat × St := unsafeWrite s (name.takeWhile (· != 0))

/-- `write(to::IO, from::IO)`, lines 989-995: `write(to, readavailable(from))` until
`eof(from)`; here `readavailable` returns the next `k ≥ 1` bytes. -/
def writeFromIO (k : Nat) (to frm : St) : Nat × St × St :=
  let rec go (fuel : Nat) (n : Nat) (to frm : St) : Nat × St × St :=
    match fuel with
    | 0 => (n, to, frm)
    | fuel + 1 =>
      if eof frm then (n, to, frm)
      else
        let chunk := frm.inp.take (max k 1)
        let frm' := { frm with pre := frm.pre ++ chunk, inp := frm.inp.drop (max k 1) }
        let (w, to') := unsafeWrite to chunk
        go fuel (n + w) to' frm'
  go (frm.inp.length + 1) 0 to frm

/-- `unsafe_read(s, p::Ref{T}, n)` and `unsafe_read(s, p::Ptr, n)`, lines 997-998. -/
def unsafeReadRef (s : St) (n : Int) : R (Bytes × St) := do
  let n ← toInt .u64 n
  unsafeRead n.toNat s
/-- `read!(s::IO, x::Ref{T})`, lines 999-1007. -/
def readRefBang {α} (isPtr isbits : Bool) (size : Nat) (readVal : St → R (α × St)) (s : St) :
    R (Sum Bytes α × St) :=
  if isPtr then .error (.errorException "read! cannot copy into a Ptr")
  else if isbits then do let (b, s') ← unsafeRead size s; pure (.inl b, s')
  else do let (v, s') ← readVal s; pure (.inr v, s')
/-- `read(s::IO, ::Type{Int8}) = reinterpret(Int8, read(s, UInt8))`, line 1009. -/
def readInt8 (s : St) : R (Int × St) := do
  let (b, s') ← readByte s
  pure (wrapInt .i8 b.toNat, s')
/-- `read(s::IO, T::Union{Type{Int16},...})`, lines 1010-1014: `unsafe_read` of `sizeof(T)`
bytes into a `Ref{T}`. -/
def readInt (t : IntTy) (s : St) : R (Int × St) := do
  let (bs, s') ← unsafeRead (t.bits / 8) s
  pure (wrapInt t (leVal bs), s')
def readFloat (nbytes : Nat) (s : St) : R (Nat × St) := do
  let (bs, s') ← unsafeRead nbytes s
  pure (leVal bs, s')
/-- `read(s::IO, ::Type{Bool}) = (read(s, UInt8) != 0)`, line 1016. -/
def readBool (s : St) : R (Bool × St) := do
  let (b, s') ← readByte s
  pure (b != 0, s')
/-- `read(s::IO, ::Type{Ptr{T}}) = convert(Ptr{T}, read(s, UInt))`, line 1017. -/
def readPtr (s : St) : R (Int × St) := readInt .u64 s

/-- `read!(s::IO, A::AbstractArray{T})`, lines 1019-1037: for `isbits` element types one
`unsafe_read` of the whole array when contiguous, else one per element; otherwise
`read(s, T)` per element. Elements are returned as their bytes (`nbytes` each). -/
def readArrayBang (isbits contiguous : Bool) (nbytes len : Nat) (s : St) : R (List Bytes × St) :=
  if isbits && contiguous then do
    let (bs, s') ← unsafeRead (nbytes * len) s
    pure ((List.range len).map (fun i => (bs.drop (i * nbytes)).take nbytes), s')
  else
    let rec go : Nat → St → R (List Bytes × St)
      | 0, s => .ok ([], s)
      | k + 1, s => do
        let (b, s1) ← unsafeRead nbytes s
        let (bs, s2) ← go k s1
        pure (b :: bs, s2)
    go len s

/-- `write(s::IO, B::BitArray) = write(s, B.chunks)`, lines 1043-1046. -/
def writeBitArray (s : St) (chunks : List Nat) : R (Nat × St) :=
  writeArray true s (chunks.map (leBytes 8))
/-- `_msk_end(n)`: the mask of the used bits of the last chunk. -/
def mskEnd (n : Nat) : Nat := if n % 64 = 0 then 2 ^ 64 - 1 else 2 ^ (n % 64) - 1
/-- `read!(s::IO, B::BitArray)`, lines 1047-1057: read the chunks; nonzero bits past
`length(B)` are cleared and raise `DimensionMismatch`. -/
def readBitArrayBang (n : Nat) (s : St) : R (List Nat × St) := do
  let nchunks := (n + 63) / 64
  let (cs, s') ← readArrayBang true true 8 nchunks s
  let chunks := cs.map leVal
  match chunks.getLast? with
  | some last =>
    if last &&& mskEnd n ≠ last then
      .error (.jl (.argumentError "DimensionMismatch: read mismatch, found non-zero bits after BitArray length"))
    else pure (chunks, s')
  | none => pure (chunks, s')

/-! ## `read(io, Char)`, lines 1091-1106 -/

/-- `leading_ones(b)` of a byte. -/
def leadingOnes (b : UInt8) : Nat :=
  if b.toNat ≥ 0xff then 8 else if b.toNat ≥ 0xfe then 7 else if b.toNat ≥ 0xfc then 6
  else if b.toNat ≥ 0xf8 then 5 else if b.toNat ≥ 0xf0 then 4 else if b.toNat ≥ 0xe0 then 3
  else if b.toNat ≥ 0xc0 then 2 else if b.toNat ≥ 0x80 then 1 else 0

/-- The `while s ≥ l && !eof(io)` loop: `s` runs over 16, 8, 0 (shift amounts); `peek(io)`
is the generic `peek`, which resets the mark. -/
def readCharLoop : List Nat → Nat → St → R (Nat × St)
  | [], c, st => .ok (c, st)
  | sh :: shs, c, st =>
    if eof st then .ok (c, st)
    else match peekByte st with
      | .error e => .error e
      | .ok (p, st1) =>
        if p.toNat / 64 = 2 then
          match readByte st1 with
          | .error e => .error e
          | .ok (b, st2) => readCharLoop shs (c + b.toNat * 2 ^ sh) st2
        else .ok (c, st1)

/-- `read(io::IO, ::Type{Char})`: the Julia `Char` as its `UInt32` representation. -/
def readChar (st : St) : R (Nat × St) := do
  let (b0, st1) ← readByte st
  let lo := leadingOnes b0
  let c := b0.toNat * 2 ^ 24
  if 2 ≤ lo ∧ lo ≤ 4 then
    -- `l = 8*(4-lo)`, `s` from 16 down to `l` by 8
    readCharLoop ([16, 8, 0].take (lo - 1)) c st1
  else pure (c, st1)

/-- The `UInt32` of a `Char` given by its (1 to 4) bytes, most significant first. -/
def packChar (bs : Bytes) : Nat :=
  (bs.getD 0 0).toNat * 2 ^ 24 + (bs.getD 1 0).toNat * 2 ^ 16 + (bs.getD 2 0).toNat * 2 ^ 8 + (bs.getD 3 0).toNat

/-- The UTF-8 structure of one character: a lead byte announcing `bs.length` bytes and
continuation bytes `0b10xxxxxx`. -/
def IsUtf8Char (bs : Bytes) : Prop :=
  match bs with
  | [b] => b.toNat < 0x80
  | [b0, b1] => 0xc0 ≤ b0.toNat ∧ b0.toNat < 0xe0 ∧ b1.toNat / 64 = 2
  | [b0, b1, b2] => 0xe0 ≤ b0.toNat ∧ b0.toNat < 0xf0 ∧ b1.toNat / 64 = 2 ∧ b2.toNat / 64 = 2
  | [b0, b1, b2, b3] => 0xf0 ≤ b0.toNat ∧ b0.toNat < 0xf8 ∧ b1.toNat / 64 = 2 ∧ b2.toNat / 64 = 2 ∧
      b3.toNat / 64 = 2
  | _ => False

/-! ## `skipchars`, lines 1643-1653 -/

/-- `skipchars(predicate, io; linecomment)`: characters are read with `read(io, Char)`
(their byte counts are `ncodeunits`); a non-matching character is pushed back with
`skip(io, -ncodeunits(c))`. `readLine` is `readline(io)`. `fuel` bounds the iterations
(each consumes at least one byte). -/
def skipchars (pred : Nat → Bool) (linecomment : Option Nat) (readLine : St → R St) :
    Nat → St → R St
  | 0, s => .ok s
  | fuel + 1, s =>
    if eof s then .ok s
    else do
      let n0 := position s
      let (c, s1) ← readChar s
      if some c = linecomment then
        let s2 ← readLine s1
        skipchars pred linecomment readLine fuel s2
      else if !pred c then skip s1 (-((position s1 - n0 : Nat) : Int))
      else skipchars pred linecomment readLine fuel s1

/-! ## Properties -/

theorem readByte_cons (s : St) (b : UInt8) (r : Bytes) (h : s.inp = b :: r) :
    readByte s = .ok (b, { s with pre := s.pre ++ [b], inp := r }) := by
  simp [readByte, h]

theorem unsafeWrite_spec (bs : Bytes) : ∀ s : St,
    unsafeWrite s bs = (bs.length, { s with out := s.out ++ bs }) := by
  induction bs with
  | nil => intro s; simp [unsafeWrite]
  | cons b bs ih =>
    intro s
    simp only [unsafeWrite, writeByte, ih]
    simp [Nat.add_comm]

theorem unsafeRead_spec (n : Nat) : ∀ s : St,
    unsafeRead n s = if n ≤ s.inp.length then
      .ok (s.inp.take n, { s with pre := s.pre ++ s.inp.take n, inp := s.inp.drop n })
    else .error .eofError := by
  induction n with
  | zero => intro s; simp [unsafeRead]
  | succ n ih =>
    intro s
    cases h : s.inp with
    | nil => simp [unsafeRead, readByte, h, bind, Except.bind]
    | cons b r =>
      simp only [unsafeRead, readByte, h, bind, Except.bind, ih]
      by_cases hn : n ≤ r.length
      · simp [hn, pure, Except.pure]
      · simp [hn, pure, Except.pure]

theorem leVal_leBytes (n : Nat) : ∀ x, x < 2 ^ (8 * n) → leVal (leBytes n x) = x := by
  induction n with
  | zero => intro x hx; simp at hx; simp [leBytes, leVal, hx]
  | succ n ih =>
    intro x hx
    have h1 : x / 256 < 2 ^ (8 * n) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      have : 2 ^ (8 * (n + 1)) = 2 ^ (8 * n) * 256 := by
        rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
      omega
    simp only [leBytes, leVal, ih _ h1]
    have : (x % 256).toUInt8.toNat = x % 256 := by
      simp [Nat.toUInt8, UInt8.toNat_ofNat]
    rw [this]; omega

theorem leBytes_length (n : Nat) : ∀ x, (leBytes n x).length = n := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; simp [leBytes, ih]

theorem toUInt8_mod (u : Nat) (b : UInt8) (h : u % 256 = b.toNat) : (u % 256).toUInt8 = b := by
  apply UInt8.toNat.inj
  simp [Nat.toUInt8, UInt8.toNat_ofNat]; omega

theorem readGo_spec (nb : Nat) : ∀ len (s : St), nb * len ≤ s.inp.length →
    readArrayBang.go nb len s = .ok ((List.range len).map (fun i => (s.inp.drop (i * nb)).take nb),
      { s with pre := s.pre ++ s.inp.take (nb * len), inp := s.inp.drop (nb * len) }) := by
  intro len
  induction len with
  | zero => intro s _; simp [readArrayBang.go]
  | succ k ih =>
    intro s h
    have h1 : nb ≤ s.inp.length := by
      have : nb ≤ nb * (k + 1) := Nat.le_mul_of_pos_right nb (by omega)
      omega
    simp only [readArrayBang.go, bind, Except.bind, unsafeRead_spec, if_pos h1]
    have h2 : nb * k ≤ (s.inp.drop nb).length := by
      simp; rw [Nat.mul_succ] at h; omega
    rw [ih _ h2]
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [List.range_succ_eq_map]
      simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]
    · simp [List.drop_drop, List.take_add, Nat.mul_succ, Nat.add_comm]

theorem writeCharLoop_step (s : St) (u n : Nat) (b : UInt8) (hb : u % 256 = b.toNat) :
    writeCharLoop s u n = if u / 256 = 0 then (n + 1, { s with out := s.out ++ [b] })
      else writeCharLoop { s with out := s.out ++ [b] } (u / 256) (n + 1) := by
  rw [writeCharLoop]; simp [writeByte, toUInt8_mod u b hb]

theorem lo_ascii (b : UInt8) (h : b.toNat < 0x80) : leadingOnes b = 0 := by
  unfold leadingOnes; repeat rw [if_neg (by omega)]
theorem lo_two (b : UInt8) (h1 : 0xc0 ≤ b.toNat) (h2 : b.toNat < 0xe0) : leadingOnes b = 2 := by
  unfold leadingOnes; repeat rw [if_neg (by omega)]
  rw [if_pos (by omega)]
theorem lo_three (b : UInt8) (h1 : 0xe0 ≤ b.toNat) (h2 : b.toNat < 0xf0) : leadingOnes b = 3 := by
  unfold leadingOnes; repeat rw [if_neg (by omega)]
  rw [if_pos (by omega)]
theorem lo_four (b : UInt8) (h1 : 0xf0 ≤ b.toNat) (h2 : b.toNat < 0xf8) : leadingOnes b = 4 := by
  unfold leadingOnes; repeat rw [if_neg (by omega)]
  rw [if_pos (by omega)]


theorem peekByte_cons (s : St) (b : UInt8) (r : Bytes) (hs : s.seekable = true) (h : s.inp = b :: r) :
    peekByte s = .ok (b, { s with mark := -1 }) := by
  cases s
  simp_all [peekByte, peek, mark, readByte, reset, ismarked, seek, position, bind, Except.bind,
    pure, Except.pure]

theorem readCharLoop_cont (sh : Nat) (shs : List Nat) (c : Nat) (st : St) (b : UInt8) (r : Bytes)
    (hs : st.seekable = true) (h : st.inp = b :: r) (hb : b.toNat / 64 = 2) :
    readCharLoop (sh :: shs) c st = readCharLoop shs (c + b.toNat * 2 ^ sh)
      { st with mark := -1, pre := st.pre ++ [b], inp := r } := by
  simp [readCharLoop, eof, h, peekByte_cons st b r hs h, hb, readByte]

theorem takeWhile_ne0 (b : Bytes) (hb : 0 ∉ b) : b.takeWhile (· != 0) = b := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ 0 := fun e => hb (e ▸ List.mem_cons_self ..)
    simp [List.takeWhile_cons, hx, ih (fun m => hb (List.mem_cons_of_mem _ m))]

theorem writeFromIO_go (k : Nat) : ∀ fuel n (to frm : St), frm.inp.length < fuel →
    writeFromIO.go k fuel n to frm =
      (n + frm.inp.length, { to with out := to.out ++ frm.inp }, { frm with pre := frm.pre ++ frm.inp, inp := [] }) := by
  intro fuel
  induction fuel with
  | zero => intro n to frm h; omega
  | succ f ih =>
    intro n to frm h
    cases hi : frm.inp with
    | nil => cases frm; simp_all [writeFromIO.go, eof]
    | cons b r =>
      simp only [writeFromIO.go, eof, hi, List.isEmpty_cons, Bool.false_eq_true, if_false, unsafeWrite_spec]
      rw [ih]
      · simp only [Prod.mk.injEq]
        refine ⟨?_, ?_, ?_⟩
        · simp only [List.length_drop, List.length_take, List.length_cons]
          have : 1 ≤ max k 1 := Nat.le_max_right _ _
          rw [Nat.min_def]; split <;> omega
        · simp [List.take_append_drop]
        · simp [List.take_append_drop]
      · simp only [List.length_drop, List.length_cons]; rw [hi] at h; simp at h
        have : 1 ≤ max k 1 := Nat.le_max_right _ _
        omega

theorem packChar_one (b : UInt8) : packChar [b] = b.toNat * 2 ^ 24 := by simp [packChar]

theorem foldl_bytes (g : Nat × St → UInt8 → Nat × St)
    (hg : ∀ acc x, g acc x = (acc.1 + 1, { acc.2 with out := acc.2.out ++ [x] })) (xs : Bytes) :
    ∀ n st, xs.foldl g (n, st) = (n + xs.length, { st with out := st.out ++ xs }) := by
  induction xs with
  | nil => intro n st; simp
  | cons x xs ih =>
    intro n st
    simp only [List.foldl_cons, hg]
    rw [ih]
    refine Prod.ext ?_ ?_ <;> simp <;> omega

theorem foldl_chunks (g : Nat × St → Bytes → Nat × St)
    (hg : ∀ acc e, g acc e = (acc.1 + e.length, { acc.2 with out := acc.2.out ++ e })) (es : List Bytes) :
    ∀ n st, es.foldl g (n, st) = (n + es.flatten.length, { st with out := st.out ++ es.flatten }) := by
  induction es with
  | nil => intro n st; simp
  | cons e es ih =>
    intro n st
    simp only [List.foldl_cons, hg]
    rw [ih]
    refine Prod.ext ?_ ?_ <;> simp <;> omega

/-! ### `SystemError` and trivial methods -/

/-- `SystemError(p, e, extrainfo)` stores its fields, converting `e` to `Int32`. -/
def SystemError3Correct : Prop :=
  (∀ p e x, -2147483648 ≤ e → e ≤ 2147483647 → systemError3 p e x = .ok ⟨p, e, x⟩) ∧
  (∀ p e x, (e < -2147483648 ∨ 2147483647 < e) → systemError3 p e x = .error (.jl (.inexactError "Int32")))
theorem systemError3Correct : SystemError3Correct := by
  refine ⟨?_, ?_⟩
  · intro p e x h1 h2
    simp [systemError3, toInt_i32 e h1 h2, bind, Except.bind, pure, Except.pure]
  · intro p e x h
    rw [systemError3, toInt_err .i32 e (by simp; omega)]; rfl

/-- `SystemError(p, e)` has `extrainfo === nothing`. -/
def SystemError2Correct : Prop :=
  ∀ p e, -2147483648 ≤ e → e ≤ 2147483647 → systemError2 p e = .ok ⟨p, e, none⟩
theorem systemError2Correct : SystemError2Correct := fun p e h1 h2 => systemError3Correct.1 p e none h1 h2

/-- `SystemError(p)` records the current `errno` and no extra information. -/
def SystemError1Correct : Prop :=
  ∀ errno p, -2147483648 ≤ errno → errno ≤ 2147483647 → systemError1 errno p = .ok ⟨p, errno, none⟩
theorem systemError1Correct : SystemError1Correct := fun errno p h1 h2 => systemError3Correct.1 p errno none h1 h2

/-- `buffer_writes(x::IO, bufsize)` returns the stream unchanged. -/
def BufferWritesIdentity : Prop := ∀ s n, bufferWrites s n = s
theorem bufferWritesIdentity : BufferWritesIdentity := fun _ _ => rfl

/-- `isreadable(io::IO)` and `iswritable(io::IO)` are `isopen(io)`. -/
def IsreadableOpen : Prop := ∀ s, isreadable s = s.isopen
theorem isreadableOpen : IsreadableOpen := fun _ => rfl
def IswritableOpen : Prop := ∀ s, iswritable s = s.isopen
theorem iswritableOpen : IswritableOpen := fun _ => rfl

/-- `isreadonly(s)` holds exactly for readable, non-writable streams. -/
def IsreadonlyCorrect : Prop := ∀ r w, isreadonly r w = true ↔ r = true ∧ w = false
theorem isreadonlyCorrect : IsreadonlyCorrect := by intro r w; cases r <;> cases w <;> decide

/-- The fallbacks throw: `read(s, Union{})`, `peek(s, Union{})`, byte I/O on a type without
it, `write(io, x)` for an unsupported `x`, and `read(s, T)` for an unsupported `T`. -/
def ReadUnionThrows : Prop := ∀ (α : Type) (s : St), (readUnion s : R α) = .error (.errorException "cannot read a value of type Union{}")
theorem readUnionThrows : ReadUnionThrows := fun _ _ => rfl
def PeekUnionThrows : Prop := ∀ (α : Type) (s : St), (peekUnion s : R α) = .error (.methodError "peek")
theorem peekUnionThrows : PeekUnionThrows := fun _ _ => rfl
def ByteIOFallbackThrows : Prop :=
  ∀ (α : Type) t, (readByteFallback t : R α) = .error (.errorException (t ++ " does not support byte I/O"))
theorem byteIOFallbackThrows : ByteIOFallbackThrows := fun _ _ => rfl
def WriteFallbackThrows : Prop := ∀ (α : Type), (writeFallback : R α) = .error (.methodError "write")
theorem writeFallbackThrows : WriteFallbackThrows := fun _ => rfl
def ReadTypeFallbackThrows : Prop := ∀ (α : Type) t, (readTypeFallback t : R α) =
  .error (.errorException ("The IO stream does not support reading objects of type " ++ t ++ "."))
theorem readTypeFallbackThrows : ReadTypeFallbackThrows := fun _ _ => rfl

/-- `writepartial(io, x)` is `write(io, x)` for a generic stream. -/
def WritepartialIsWrite : Prop := ∀ (α : Type) (w : St → α) s, writepartial w s = w s
theorem writepartialIsWrite : WritepartialIsWrite := fun _ _ _ => rfl

/-! ### Byte loops -/

/-- `unsafe_write(s, p, n)` appends the `n` bytes and returns `n`. -/
def UnsafeWriteAppends : Prop := ∀ s bs, unsafeWrite s bs = (bs.length, { s with out := s.out ++ bs })
theorem unsafeWriteAppends : UnsafeWriteAppends := fun s bs => unsafeWrite_spec bs s

/-- `unsafe_read(s, p, n)` stores the next `n` bytes, or throws `EOFError` if fewer remain. -/
def UnsafeReadNext : Prop :=
  (∀ n s, n ≤ s.inp.length → unsafeRead n s =
      .ok (s.inp.take n, { s with pre := s.pre ++ s.inp.take n, inp := s.inp.drop n })) ∧
  (∀ n s, s.inp.length < n → unsafeRead n s = .error .eofError)
theorem unsafeReadNext : UnsafeReadNext := by
  refine ⟨?_, ?_⟩
  · intro n s h; rw [unsafeRead_spec, if_pos h]
  · intro n s h; rw [unsafeRead_spec, if_neg (by omega)]

/-- `unsafe_write(s, p::Ptr, n)` converts `n` to `UInt` and writes that many bytes;
`unsafe_write(s, p::Ref, n)` converts the reference and does the same. -/
def UnsafeWritePtrCorrect : Prop :=
  (∀ s mem n, 0 ≤ n → n ≤ 18446744073709551615 → unsafeWriteRef s mem n = .ok (unsafeWrite s (mem.take n.toNat))) ∧
  (∀ s mem n, n < 0 → unsafeWriteRef s mem n = .error (.jl (.inexactError "UInt64")))
theorem unsafeWritePtrCorrect : UnsafeWritePtrCorrect := by
  refine ⟨?_, ?_⟩
  · intro s mem n h1 h2; simp [unsafeWriteRef, toInt_u64 n h1 h2, bind, Except.bind, pure, Except.pure]
  · intro s mem n h; simp [unsafeWriteRef, toInt_u64_neg n h, bind, Except.bind]

/-- `unsafe_read(s, p::Ptr, n)` and `unsafe_read(s, p::Ref, n)` convert `n` to `UInt` and
read that many bytes. -/
def UnsafeReadPtrCorrect : Prop :=
  (∀ s n, 0 ≤ n → n ≤ 18446744073709551615 → unsafeReadRef s n = unsafeRead n.toNat s) ∧
  (∀ s n, n < 0 → unsafeReadRef s n = .error (.jl (.inexactError "UInt64")))
theorem unsafeReadPtrCorrect : UnsafeReadPtrCorrect := by
  refine ⟨?_, ?_⟩
  · intro s n h1 h2; simp [unsafeReadRef, toInt_u64 n h1 h2, bind, Except.bind]
  · intro s n h; simp [unsafeReadRef, toInt_u64_neg n h, bind, Except.bind]

/-! ### `mark`, `unmark`, `reset`, `ismarked`, `peek` -/

/-- `mark(s)` returns the position and marks the stream. -/
def MarkCorrect : Prop := ∀ s, (mark s).1 = position s ∧ ismarked (mark s).2 = true ∧ (mark s).2.inp = s.inp
theorem markCorrect : MarkCorrect := fun s => ⟨rfl, by simp [mark, ismarked], rfl⟩

/-- `ismarked(s)` holds exactly when `s.mark ≥ 0`. -/
def IsmarkedCorrect : Prop := ∀ s, ismarked s = true ↔ 0 ≤ s.mark
theorem ismarkedCorrect : IsmarkedCorrect := fun s => by simp [ismarked]

/-- `unmark(s)` returns whether `s` was marked and leaves it unmarked. -/
def UnmarkCorrect : Prop := ∀ s, (unmark s).1 = ismarked s ∧ ismarked (unmark s).2 = false ∧ (unmark s).2.inp = s.inp
theorem unmarkCorrect : UnmarkCorrect := by
  intro s; by_cases h : ismarked s = true
  · have h' : ¬ s.mark < 0 := by simp [ismarked] at h; omega
    simp [unmark, ismarked, h']; omega
  · simp at h; simp [unmark, h]

/-- `reset(s)` throws on an unmarked stream; after `mark` and reading `k` bytes it returns
the marked position, goes back to it, and removes the mark. -/
def ResetCorrect : Prop :=
  (∀ s, ismarked s = false → reset s = argErr "not marked") ∧
  (∀ s k, s.seekable = true → k ≤ s.inp.length →
      ∃ s', (do let (_, s1) ← unsafeRead k (mark s).2; reset s1) = .ok ((position s : Int), s') ∧
        s'.pre = s.pre ∧ s'.inp = s.inp ∧ ismarked s' = false)
theorem resetCorrect : ResetCorrect := by
  refine ⟨fun s h => by simp [reset, h], ?_⟩
  intro s k hs hk
  refine ⟨{ s with mark := -1 }, ?_, rfl, rfl, by simp [ismarked]⟩
  simp [mark, unsafeRead_spec, hk, reset, ismarked, seek, hs, position, bind, Except.bind, pure, Except.pure]

/-- `peek(s)` returns the next byte without consuming it. -/
def PeekByteCorrect : Prop :=
  ∀ s b r, s.seekable = true → s.inp = b :: r → ∃ s', peekByte s = .ok (b, s') ∧ s'.pre = s.pre ∧ s'.inp = s.inp
theorem peekByteCorrect : PeekByteCorrect := fun s b r hs h => ⟨_, peekByte_cons s b r hs h, rfl, rfl⟩

/-! ### `open_flags` and `open(f, ...)` -/

/-- The documented defaults of `open`'s keyword table (`base/iostream.jl:292-300`):
`read = !write`, `write = truncate | append`, `truncate = !read & write`, `append = false`. -/
def OpenFlagsDoc : Prop :=
  ∀ r w c t a : Option Bool,
    let f := openFlags r w c t a
    f.write = w.getD (t.getD false || a.getD false) ∧ f.read = r.getD (!f.write) ∧
    f.truncate = t.getD (!f.read && f.write) ∧ f.append = a.getD false

theorem openFlagsDoc_refuted : ¬ OpenFlagsDoc := by
  intro h
  have := (h none none none none (some true)).2.2.1
  revert this; decide

/-- Without `append`, `open_flags` follows the documented table, and `create` defaults to
`!read & write | truncate`. -/
def OpenFlagsTable : Prop :=
  ∀ r w c t : Option Bool,
    let f := openFlags r w c t none
    f.write = w.getD (t.getD false) ∧ f.read = r.getD (!f.write) ∧
    f.truncate = t.getD (!f.read && f.write) ∧ f.append = false ∧
    f.create = c.getD ((!f.read && f.write) || t.getD false)

theorem openFlagsTable : OpenFlagsTable := by
  intro r w c t
  rcases r with _ | ⟨_ | _⟩ <;> rcases w with _ | ⟨_ | _⟩ <;> rcases c with _ | ⟨_ | _⟩ <;>
    rcases t with _ | ⟨_ | _⟩ <;> decide

/-- `open(f, args...)` returns `f`'s result and closes the stream `f` leaves, also when
`f` throws; a failing `open` is propagated. -/
def OpenDoCloses : Prop :=
  (∀ (α : Type) (e : Err) (f : St → R α × St), openDo (.error e) f = (.error e, none)) ∧
  (∀ (α : Type) (io : St) (f : St → R α × St),
      (openDo (.ok io) f).1 = (f io).1 ∧ (openDo (.ok io) f).2 = some { (f io).2 with isopen := false })
theorem openDoCloses : OpenDoCloses := ⟨fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

/-! ### `AbstractPipe` -/

/-- `getproperty(pipe, name)` returns the field, asserting that the stream fields are `IO`. -/
def PipeGetpropertyCorrect : Prop :=
  (∀ (α : Type) (g : String → α) isIO name, name ∉ ["in", "in_stream", "out", "out_stream", "err", "err_stream"] →
      pipeGetproperty g isIO name = .ok (g name)) ∧
  (∀ (α : Type) (g : String → α) isIO name, name ∈ ["in", "in_stream", "out", "out_stream", "err", "err_stream"] →
      pipeGetproperty g isIO name = if isIO (g name) then .ok (g name) else .error (.typeError "typeassert"))
theorem pipeGetpropertyCorrect : PipeGetpropertyCorrect := by
  refine ⟨?_, ?_⟩
  · intro α g isIO name h; simp only [pipeGetproperty, if_neg h]
  · intro α g isIO name h; simp only [pipeGetproperty, if_pos h]

/-- `iswritable(pipe)` is `iswritable(pipe_writer(pipe))`. -/
def PipeIswritable : Prop := ∀ p, pipeIswritable p = iswritable p.wr
theorem pipeIswritable_eq : PipeIswritable := fun _ => rfl

/-- `flush`/`closewrite(pipe)` act on the writer only. -/
def PipeFlushWriter : Prop :=
  ∀ f p u s, f p.wr = .ok (u, s) → pipeFlushLike f p = .ok (u, { p with wr := s })
theorem pipeFlushWriter : PipeFlushWriter := by
  intro f p u s h; simp [pipeFlushLike, onWriter, pipeWriter, h, bind, Except.bind, pure, Except.pure]

/-- `write(pipe, b::UInt8)` appends `b` to the writer and leaves the reader. -/
def PipeWriteByte : Prop := ∀ p b, pipeWriteByte p b = .ok (1, { p with wr := { p.wr with out := p.wr.out ++ [b] } })
theorem pipeWriteByte_eq : PipeWriteByte := by
  intro p b; simp [pipeWriteByte, onWriter, writeByte, pipeWriter, bind, Except.bind, pure, Except.pure]

/-- `writepartial(pipe, x)` is `writepartial` on the writer. -/
def PipeWritepartial : Prop :=
  ∀ (α : Type) (w : St → R (α × St)) p a s, w p.wr = .ok (a, s) → pipeWritepartial w p = .ok (a, { p with wr := s })
theorem pipeWritepartial_eq : PipeWritepartial := by
  intro α w p a s h; simp [pipeWritepartial, onWriter, writepartial, pipeWriter, h, bind, Except.bind, pure, Except.pure]

/-- `write(to, from::AbstractPipe)` writes from the pipe's reader. -/
def WriteFromPipeReader : Prop := ∀ (α : Type) (w : St → St → α) to p, writeFromPipe w to p = w to p.rd
theorem writeFromPipeReader : WriteFromPipeReader := fun _ _ _ _ => rfl

/-- `unsafe_write(pipe, p, n)` appends to the writer and returns `n`. -/
def PipeUnsafeWrite : Prop := ∀ p bs, pipeUnsafeWrite p bs = .ok (bs.length, { p with wr := { p.wr with out := p.wr.out ++ bs } })
theorem pipeUnsafeWrite_eq : PipeUnsafeWrite := by
  intro p bs; simp [pipeUnsafeWrite, onWriter, unsafeWrite_spec, pipeWriter, bind, Except.bind, pure, Except.pure]

/-- `buffer_writes(pipe, args...)` is `buffer_writes` of the writer. -/
def PipeBufferWrites : Prop := ∀ p, pipeBufferWrites p = p.wr
theorem pipeBufferWrites_eq : PipeBufferWrites := fun _ => rfl

/-- The `@eval`-generated `mark`, `unmark`, `reset`, `ismarked`, `read`, `bytesavailable`,
`reseteof`, `isreadable` on a pipe act on the reader only. -/
def PipeReaderOps : Prop :=
  ∀ (α : Type) (f : St → R (α × St)) p a s, f p.rd = .ok (a, s) → pipeReaderOp f p = .ok (a, { p with rd := s })
theorem pipeReaderOps : PipeReaderOps := by
  intro α f p a s h; simp [pipeReaderOp, onReader, pipeReader, h, bind, Except.bind, pure, Except.pure]

/-- `readavailable(pipe)` reads from the reader. -/
def PipeReadavailable : Prop :=
  ∀ ra p a s, ra p.rd = .ok (a, s) → pipeReadavailable ra p = .ok (a, { p with rd := s })
theorem pipeReadavailable_eq : PipeReadavailable := by
  intro ra p a s h; simp [pipeReadavailable, onReader, pipeReader, h, bind, Except.bind, pure, Except.pure]

/-- `read(pipe, UInt8)` reads the reader's next byte. -/
def PipeReadByte : Prop :=
  ∀ p b r, p.rd.inp = b :: r → pipeReadByte p = .ok (b, { p with rd := { p.rd with pre := p.rd.pre ++ [b], inp := r } })
theorem pipeReadByte_eq : PipeReadByte := by
  intro p b r h; simp [pipeReadByte, onReader, readByte, pipeReader, h, bind, Except.bind, pure, Except.pure]

/-- `unsafe_read(pipe, p, n)` reads `n` bytes of the reader. -/
def PipeUnsafeRead : Prop :=
  ∀ p n, n ≤ p.rd.inp.length → pipeUnsafeRead p n =
    .ok (p.rd.inp.take n, { p with rd := { p.rd with pre := p.rd.pre ++ p.rd.inp.take n, inp := p.rd.inp.drop n } })
theorem pipeUnsafeRead_eq : PipeUnsafeRead := by
  intro p n h; simp [pipeUnsafeRead, onReader, unsafeRead_spec, h, pipeReader, bind, Except.bind, pure, Except.pure]

/-- `copyuntil(out, pipe, delim)` (each delimiter type), `readuntil_vector!(pipe, ...)`,
`readbytes!(pipe, ...)`, `peek(pipe, T)` and `wait_readnb(pipe, nb)` forward the same
arguments to `pipe_reader(pipe)`. -/
def PipeForwardReader : Prop :=
  ∀ (α : Type) (op : St → R (α × St)) p a s, op p.rd = .ok (a, s) → pipeForward op p = .ok (a, { p with rd := s })
theorem pipeForwardReader : PipeForwardReader := by
  intro α op p a s h; simp [pipeForward, onReader, pipeReader, h, bind, Except.bind, pure, Except.pure]

/-- `eof(pipe)` is `eof(pipe_reader(pipe))`. -/
def PipeEof : Prop := ∀ p, pipeEof p = eof p.rd
theorem pipeEof_eq : PipeEof := fun _ => rfl

/-- `isopen(pipe)` holds while either side is open. -/
def PipeIsopen : Prop := ∀ p, pipeIsopen p = true ↔ p.wr.isopen = true ∨ p.rd.isopen = true
theorem pipeIsopen_iff : PipeIsopen := fun p => by simp [pipeIsopen, pipeWriter, pipeReader]

/-- `close(pipe)` closes both sides, so the pipe is no longer open. -/
def PipeCloseBoth : Prop := ∀ p, (pipeClose p).wr.isopen = false ∧ (pipeClose p).rd.isopen = false ∧ pipeIsopen (pipeClose p) = false
theorem pipeCloseBoth : PipeCloseBoth := fun p => by simp [pipeClose, close, pipeIsopen, pipeWriter, pipeReader]

/-- `wait_close(pipe)` waits for the writer, then the reader. -/
def PipeWaitClose : Prop := ∀ wc p, pipeWaitClose wc p = wc p.wr ++ wc p.rd
theorem pipeWaitClose_eq : PipeWaitClose := fun _ _ => rfl

/-! ### Binary I/O -/

/-- `write(io, x1, xs...)` writes each argument in order and returns the total count. -/
def WriteManyCorrect : Prop :=
  ∀ s (b : UInt8) bs, writeMany writeByte s b bs = (bs.length + 1, { s with out := s.out ++ b :: bs })
theorem writeManyCorrect : WriteManyCorrect := by
  intro s b bs
  simp only [writeMany, writeByte]
  rw [foldl_bytes _ (fun acc x => rfl)]
  refine Prod.ext ?_ ?_ <;> simp <;> omega

/-- `write(s, x::Ref{T})` throws for a `Ptr`, writes the `sizeof(T)` bytes of `isbits`
contents, and otherwise writes `x[]`. -/
def WriteRefCorrect : Prop :=
  (∀ ib bytes (wv : St → R (Nat × St)) s, writeRef true ib bytes wv s = .error (.errorException "write cannot copy from a Ptr")) ∧
  (∀ bytes (wv : St → R (Nat × St)) s, writeRef false true bytes wv s = .ok (bytes.length, { s with out := s.out ++ bytes })) ∧
  (∀ bytes (wv : St → R (Nat × St)) s, writeRef false false bytes wv s = wv s)
theorem writeRefCorrect : WriteRefCorrect :=
  ⟨fun _ _ _ _ => rfl, fun bytes wv s => by simp [writeRef, unsafeWrite_spec], fun _ _ _ => rfl⟩

/-- `write(s, x::Int16..Float64)` emits the `sizeof(x)` little-endian bytes and `read(s, T)`
returns the value. -/
def WriteReadInt : Prop :=
  ∀ t : IntTy, ∀ s x rest, t.min ≤ x → x ≤ t.max →
    let bs := leBytes (t.bits / 8) (bitsOf t x)
    writeInt t s x = (t.bits / 8, { s with out := s.out ++ bs }) ∧
    (readInt t (St.of (bs ++ rest))).map Prod.fst = .ok x
theorem writeReadInt : WriteReadInt := by
  intro t s x rest h1 h2
  have hb : bitsOf t x < 2 ^ (8 * (t.bits / 8)) := by
    cases t <;> simp [bitsOf, IntTy.bits, IntTy.min, IntTy.max] at h1 h2 ⊢ <;> omega
  refine ⟨by simp [writeInt, unsafeWrite_spec, leBytes_length], ?_⟩
  simp only [readInt, St.of, bind, Except.bind, unsafeRead_spec, List.length_append, leBytes_length,
    Nat.le_add_right, if_true, List.take_left' (leBytes_length _ _), pure, Except.pure, Except.map,
    leVal_leBytes _ _ hb]
  cases t <;> simp [bitsOf, wrapInt, IntTy.bits, IntTy.min, IntTy.max, IntTy.signed] at h1 h2 ⊢ <;> omega

/-- Floats: the bit pattern is written little-endian and read back unchanged. -/
def WriteReadFloat : Prop :=
  ∀ n s bits rest, bits < 2 ^ (8 * n) →
    writeFloat n s bits = (n, { s with out := s.out ++ leBytes n bits }) ∧
    (readFloat n (St.of (leBytes n bits ++ rest))).map Prod.fst = .ok bits
theorem writeReadFloat : WriteReadFloat := by
  intro n s bits rest h
  refine ⟨by simp [writeFloat, unsafeWrite_spec, leBytes_length], ?_⟩
  simp only [readFloat, St.of, bind, Except.bind, unsafeRead_spec, List.length_append, leBytes_length,
    Nat.le_add_right, if_true, List.take_left' (leBytes_length _ _), pure, Except.pure, Except.map,
    leVal_leBytes _ _ h]

/-- `write(s, x::Int8)` writes one byte and `read(s, Int8)` returns `x`. -/
def WriteReadInt8 : Prop :=
  ∀ s x rest, -128 ≤ x → x ≤ 127 →
    writeInt8 s x = (1, { s with out := s.out ++ [(bitsOf .i8 x).toUInt8] }) ∧
    (readInt8 (St.of ((bitsOf .i8 x).toUInt8 :: rest))).map Prod.fst = .ok x
theorem writeReadInt8 : WriteReadInt8 := by
  intro s x rest h1 h2
  refine ⟨rfl, ?_⟩
  have : ((bitsOf .i8 x).toUInt8).toNat = bitsOf .i8 x := by
    simp [bitsOf, IntTy.bits, Nat.toUInt8, UInt8.toNat_ofNat]; omega
  simp [readInt8, St.of, readByte, bind, Except.bind, pure, Except.pure, Except.map, this]
  simp [bitsOf, wrapInt, IntTy.bits, IntTy.signed]; omega

/-- `write(s, b::Bool)` writes 0 or 1 and `read(s, Bool)` returns `b`. -/
def WriteReadBool : Prop :=
  ∀ s b rest, writeBool s b = (1, { s with out := s.out ++ [if b then 1 else 0] }) ∧
    (readBool (St.of ((if b then 1 else 0) :: rest))).map Prod.fst = .ok b
theorem writeReadBool : WriteReadBool := by
  intro s b rest
  refine ⟨rfl, ?_⟩
  cases b <;> simp [readBool, St.of, readByte, bind, Except.bind, pure, Except.pure, Except.map]

/-- `read(s, Bool)` is `true` exactly for a nonzero byte. -/
def ReadBoolNonzero : Prop :=
  ∀ (b : UInt8) rest, (readBool (St.of (b :: rest))).map Prod.fst = .ok (b != 0)
theorem readBoolNonzero : ReadBoolNonzero := by
  intro b rest; simp [readBool, St.of, readByte, bind, Except.bind, pure, Except.pure, Except.map]

/-- `write(to, p::Ptr)` writes the address as a `UInt`; `read(s, Ptr{T})` reads it back. -/
def WriteReadPtr : Prop :=
  ∀ s p rest, p < 2 ^ 64 →
    writePtr s p = (8, { s with out := s.out ++ leBytes 8 p }) ∧
    (readPtr (St.of (leBytes 8 p ++ rest))).map Prod.fst = .ok (p : Int)
theorem writeReadPtr : WriteReadPtr := by
  intro s p rest h
  have := writeReadInt .u64 s p rest (by simp) (by simp; omega)
  have hb : bitsOf .u64 (p : Int) = p := by simp [bitsOf, IntTy.bits]; omega
  simp only [hb] at this
  exact ⟨this.1, this.2⟩

/-- `write(s, A::AbstractArray)` writes every element's bytes in order and returns the
total, and throws for non-`isbits` element types. -/
def WriteArrayCorrect : Prop :=
  (∀ s elems, writeArray true s elems = .ok (elems.flatten.length, { s with out := s.out ++ elems.flatten })) ∧
  (∀ s elems, writeArray false s elems = .error (.errorException "`write` is not supported on non-isbits arrays"))
theorem writeArrayCorrect : WriteArrayCorrect := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro s elems
  simp only [writeArray, Bool.not_true, Bool.false_eq_true, if_false]
  rw [foldl_chunks _ (fun acc e => by simp [unsafeWrite_spec])]
  simp

/-- `write(s, B::BitArray)` writes the 64-bit chunks, little-endian. -/
def WriteBitArrayChunks : Prop :=
  ∀ s chunks, writeBitArray s chunks = .ok ((chunks.map (leBytes 8)).flatten.length,
    { s with out := s.out ++ (chunks.map (leBytes 8)).flatten })
theorem writeBitArrayChunks : WriteBitArrayChunks := fun s chunks => writeArrayCorrect.1 s _

/-- `read!(s, x::Ref{T})` throws for a `Ptr`, reads `sizeof(T)` bytes of `isbits`
contents, and otherwise stores `read(s, T)`. -/
def ReadRefCorrect : Prop :=
  (∀ (α : Type) ib size (rv : St → R (α × St)) s, readRefBang true ib size rv s = .error (.errorException "read! cannot copy into a Ptr")) ∧
  (∀ (α : Type) size (rv : St → R (α × St)) s, size ≤ s.inp.length →
      (readRefBang false true size rv s).map Prod.fst = .ok (.inl (s.inp.take size))) ∧
  (∀ (α : Type) size (rv : St → R (α × St)) s v s', rv s = .ok (v, s') →
      readRefBang false false size rv s = .ok (.inr v, s'))
theorem readRefCorrect : ReadRefCorrect := by
  refine ⟨fun _ _ _ _ _ => rfl, ?_, ?_⟩
  · intro α size rv s h
    simp [readRefBang, unsafeRead_spec, h, bind, Except.bind, pure, Except.pure, Except.map]
  · intro α size rv s v s' h
    simp [readRefBang, h, bind, Except.bind, pure, Except.pure]

/-- `read!(s, A::AbstractArray)`: the contiguous fast path reads the same elements as the
element loop, namely consecutive `nb`-byte pieces of the input. -/
def ReadArrayCorrect : Prop :=
  (∀ nb len (s : St), nb * len ≤ s.inp.length → readArrayBang true true nb len s = readArrayBang true false nb len s) ∧
  (∀ nb len (s : St), nb * len ≤ s.inp.length →
      (readArrayBang true false nb len s).map Prod.fst = .ok ((List.range len).map (fun i => (s.inp.drop (i * nb)).take nb)))
theorem readArrayCorrect : ReadArrayCorrect := by
  refine ⟨?_, ?_⟩
  · intro nb len s h
    simp only [readArrayBang, Bool.and_self, Bool.and_false, Bool.false_eq_true, if_true, if_false,
      bind, Except.bind, unsafeRead_spec, if_pos h, pure, Except.pure]
    rw [readGo_spec nb len s h]
    simp only [Except.ok.injEq, Prod.mk.injEq, and_true]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rw [List.drop_take, List.take_take]
    congr 1
    have : (i + 1) * nb ≤ nb * len := by rw [Nat.mul_comm nb]; exact Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this; omega
  · intro nb len s h
    simp only [readArrayBang, Bool.and_false, Bool.false_eq_true, if_false]
    rw [readGo_spec nb len s h]; rfl

/-- `read!(s, B::BitArray)` with a last chunk that has bits set beyond `length(B)` throws
`DimensionMismatch`; chunks with no such bits are returned unchanged. -/
def ReadBitArrayCorrect : Prop :=
  (∀ n (s : St) cs s', readArrayBang true true 8 ((n + 63) / 64) s = .ok (cs, s') →
      ∀ last, (cs.map leVal).getLast? = some last → last &&& mskEnd n ≠ last →
      readBitArrayBang n s = .error (.jl (.argumentError "DimensionMismatch: read mismatch, found non-zero bits after BitArray length"))) ∧
  (∀ n (s : St) cs s', readArrayBang true true 8 ((n + 63) / 64) s = .ok (cs, s') →
      (∀ last, (cs.map leVal).getLast? = some last → last &&& mskEnd n = last) →
      readBitArrayBang n s = .ok (cs.map leVal, s'))
theorem readBitArrayCorrect : ReadBitArrayCorrect := by
  refine ⟨?_, ?_⟩
  · intro n s cs s' h last hl hm
    simp [readBitArrayBang, h, bind, Except.bind, hl, hm]
  · intro n s cs s' h hm
    simp only [readBitArrayBang, h, bind, Except.bind]
    cases hl : (cs.map leVal).getLast? with
    | none => simp [pure, Except.pure]
    | some last => simp [hm last hl, pure, Except.pure]

/-- `write(s, A::StridedArray)`: non-`isbits` element types throw, contiguous arrays are one
`unsafe_write`, a vector with stride 1 is written whole, other strides use the element
loop, and a matrix with contiguous columns `c` elements apart is written column by
column. -/
def WriteStridedCorrect : Prop :=
  (∀ c sz st mem g s, writeStrided false c sz st mem g s = .error (.errorException "`write` is not supported on non-isbits arrays")) ∧
  (∀ sz st mem g s, writeStrided true true sz st mem g s = .ok (unsafeWrite s (mem.take (sz.foldl (· * ·) 1)).flatten)) ∧
  (∀ m mem g s, writeStrided true false [m] [1] mem g s = .ok (unsafeWrite s (mem.take (1 * m)).flatten)) ∧
  (∀ m k mem g s, k ≠ 1 → writeStrided true false [m] [k] mem g s = writeArray true s g) ∧
  (∀ m k c, m ≠ 1 → k ≠ 1 → c ≠ m →
      stridedPlan true false [m, k] [1, c] = .runs ((List.range k).map (fun j => c * j)) m)
theorem writeStridedCorrect : WriteStridedCorrect := by
  refine ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro m mem g s; simp [writeStrided, stridedPlan, mergeAdjacentDim]
  · intro m k mem g s hk; simp [writeStrided, stridedPlan, mergeAdjacentDim, hk]
  · intro m k c hm hk hc
    simp [stridedPlan, mergeAdjacentDim, mergeLoop, hm, hk, Ne.symm hc, hc, cartesian, List.flatMap,
      Function.comp_def]

/-- `read!(s, A::StridedArray)`: non-`isbits` or contiguous arrays use the `AbstractArray`
method, a stride-1 vector is one `unsafe_read` of all its bytes, and other strides use
the `AbstractArray` method. -/
def ReadStridedCorrect : Prop :=
  (∀ c sz st nb s, readStrided false c sz st nb s = .ok (none, s)) ∧
  (∀ sz st nb s, readStrided true true sz st nb s = .ok (none, s)) ∧
  (∀ m nb s, nb * (1 * m) ≤ s.inp.length →
      (readStrided true false [m] [1] nb s).map Prod.fst = .ok (some [(0, s.inp.take (nb * (1 * m)))])) ∧
  (∀ m k nb s, k ≠ 1 → readStrided true false [m] [k] nb s = .ok (none, s))
theorem readStridedCorrect : ReadStridedCorrect := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_⟩
  · intro m nb s h
    rw [Nat.one_mul] at h ⊢
    simp [readStrided, stridedPlan, mergeAdjacentDim, unsafeRead_spec, h, bind, Except.bind, pure,
      Except.pure, Except.map]
  · intro m k nb s hk; simp [readStrided, stridedPlan, mergeAdjacentDim, hk]

/-- `write(io, c::Char)` emits the UTF-8 bytes of `c` and `read(io, Char)` decodes them:
writing a character and reading it back gives the same `Char`, whatever follows. -/
def CharRoundTrip : Prop :=
  ∀ bs : Bytes, IsUtf8Char bs → ∀ s rest,
    writeChar s (packChar bs) = (bs.length, { s with out := s.out ++ bs }) ∧
    (readChar (St.of (bs ++ rest))).map Prod.fst = .ok (packChar bs)

theorem charRoundTrip : CharRoundTrip := by
  intro bs hbs s rest
  have hl : ∀ b : UInt8, b.toNat < 256 := fun b => b.toNat_lt
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, t⟩⟩⟩⟩⟩ <;> simp only [IsUtf8Char] at hbs
  · have := hl b0
    refine ⟨?_, ?_⟩
    · simp only [writeChar]
      rw [show bswap32 (packChar [b0]) = b0.toNat by simp [bswap32, packChar]; omega]
      rw [writeCharLoop_step s _ 0 b0 (by omega), if_pos (by omega)]; simp
    · simp [readChar, St.of, readByte, lo_ascii b0 hbs, bind, Except.bind, pure, Except.pure, Except.map,
        packChar]
  · have := hl b0; have := hl b1
    refine ⟨?_, ?_⟩
    · simp only [writeChar]
      rw [show bswap32 (packChar [b0, b1]) = b1.toNat * 256 + b0.toNat by simp [bswap32, packChar]; omega]
      rw [writeCharLoop_step s _ 0 b0 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b1 (by omega), if_pos (by omega)]
      simp
    · simp only [readChar, St.of, readByte, List.cons_append, bind, Except.bind, lo_two b0 hbs.1 hbs.2.1]
      simp only [show (2 ≤ 2 ∧ 2 ≤ 4) by omega, if_true, show [16, 8, 0].take (2 - 1) = [16] from rfl]
      rw [readCharLoop_cont 16 [] _ _ b1 rest rfl rfl hbs.2.2]
      simp [readCharLoop, Except.map, packChar]
  · have := hl b0; have := hl b1; have := hl b2
    refine ⟨?_, ?_⟩
    · simp only [writeChar]
      rw [show bswap32 (packChar [b0, b1, b2]) = b2.toNat * 65536 + b1.toNat * 256 + b0.toNat by
        simp [bswap32, packChar]; omega]
      rw [writeCharLoop_step s _ 0 b0 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b1 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b2 (by omega), if_pos (by omega)]
      simp
    · simp only [readChar, St.of, readByte, List.cons_append, bind, Except.bind, lo_three b0 hbs.1 hbs.2.1]
      simp only [show (2 ≤ 3 ∧ 3 ≤ 4) by omega, if_true, show [16, 8, 0].take (3 - 1) = [16, 8] from rfl]
      rw [readCharLoop_cont 16 [8] _ _ b1 (b2 :: rest) rfl rfl hbs.2.2.1,
        readCharLoop_cont 8 [] _ _ b2 rest rfl rfl hbs.2.2.2]
      simp [readCharLoop, Except.map, packChar]
  · have := hl b0; have := hl b1; have := hl b2; have := hl b3
    refine ⟨?_, ?_⟩
    · simp only [writeChar]
      rw [show bswap32 (packChar [b0, b1, b2, b3]) =
          b3.toNat * 16777216 + b2.toNat * 65536 + b1.toNat * 256 + b0.toNat by
        simp [bswap32, packChar]; omega]
      rw [writeCharLoop_step s _ 0 b0 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b1 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b2 (by omega), if_neg (by omega),
        writeCharLoop_step _ _ _ b3 (by omega), if_pos (by omega)]
      simp
    · simp only [readChar, St.of, readByte, List.cons_append, bind, Except.bind, lo_four b0 hbs.1 hbs.2.1]
      simp only [show (2 ≤ 4 ∧ 4 ≤ 4) by omega, if_true, show [16, 8, 0].take (4 - 1) = [16, 8, 0] from rfl]
      rw [readCharLoop_cont 16 [8, 0] _ _ b1 (b2 :: b3 :: rest) rfl rfl hbs.2.2.1,
        readCharLoop_cont 8 [0] _ _ b2 (b3 :: rest) rfl rfl hbs.2.2.2.1,
        readCharLoop_cont 0 [] _ _ b3 rest rfl rfl hbs.2.2.2.2]
      simp [readCharLoop, Except.map, packChar]

/-- `write(io, s::Symbol)` writes the bytes of the name and returns their number. -/
def WriteSymbolCorrect : Prop := ∀ s name, 0 ∉ name → writeSymbol s name = (name.length, { s with out := s.out ++ name })
theorem writeSymbolCorrect : WriteSymbolCorrect := by
  intro s name h; simp [writeSymbol, takeWhile_ne0 name h, unsafeWrite_spec]

/-- `write(to, from)` copies all of `from` and returns the number of bytes. -/
def WriteFromIOCorrect : Prop :=
  ∀ k to frm, (writeFromIO k to frm).1 = frm.inp.length ∧ (writeFromIO k to frm).2.1.out = to.out ++ frm.inp ∧
    (writeFromIO k to frm).2.2.inp = []
theorem writeFromIOCorrect : WriteFromIOCorrect := by
  intro k to frm
  simp only [writeFromIO]
  rw [writeFromIO_go k _ 0 to frm (by omega)]
  simp

/-! ### `skipchars` -/

/-- `skipchars(predicate, io)` leaves the stream before the first character for which
`predicate` is false, for any `IO` stream. -/
def SkipcharsStreams : Prop :=
  ∀ (pred : Nat → Bool) (rl : St → R St) (s : St) (c : UInt8) (rest : Bytes),
    s.inp = c :: rest → c.toNat < 0x80 → pred (packChar [c]) = false →
    ∃ s', skipchars pred none rl (s.inp.length + 1) s = .ok s' ∧ s'.inp = s.inp

theorem skipcharsStreams_refuted : ¬ SkipcharsStreams := by
  intro h
  obtain ⟨s', hs, _⟩ := h (fun _ => false) (fun s => .ok s) { pre := [], inp := [120], seekable := false }
    120 [] rfl (by decide) rfl
  have e : skipchars (fun _ => false) none (fun s => .ok s) (([120] : Bytes).length + 1)
      ({ pre := [], inp := [120], seekable := false } : St) =
      argErr "seek failed, IOBuffer is not seekable and is not marked" := by decide
  change skipchars (fun _ => false) none (fun s => .ok s) (([120] : Bytes).length + 1)
      ({ pre := [], inp := [120], seekable := false } : St) = _ at hs
  rw [e] at hs; cases hs

/-- On a seekable stream, `skipchars` skips the leading ASCII characters satisfying the
predicate and stops before the first one that does not. -/
def SkipcharsSeekable : Prop :=
  ∀ (pred : Nat → Bool) (rl : St → R St) (ws : Bytes) (c : UInt8) (rest : Bytes) (s : St),
    s.seekable = true → s.inp = ws ++ c :: rest →
    (∀ w ∈ ws, w.toNat < 0x80 ∧ pred (packChar [w]) = true) → c.toNat < 0x80 → pred (packChar [c]) = false →
    ∃ s', skipchars pred none rl (s.inp.length + 1) s = .ok s' ∧ s'.inp = c :: rest

theorem skipcharsSeekable : SkipcharsSeekable := by
  intro pred rl ws c rest s hs hin hws hc hpc
  suffices H : ∀ fuel, ws.length < fuel → ∃ s', skipchars pred none rl fuel s = .ok s' ∧ s'.inp = c :: rest by
    exact H _ (by rw [hin]; simp; omega)
  rw [packChar_one] at hpc
  induction ws generalizing s with
  | nil =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp at hin
    have e : ((s.pre.length : Int) + 1 + -1).toNat = s.pre.length := by omega
    simp [skipchars, eof, hin, readChar, readByte, lo_ascii c hc, hpc, skip, seek, hs, position, bind,
      Except.bind, pure, Except.pure, e]
  | cons w ws ih =>
    intro fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hw := hws w (by simp)
    rw [packChar_one] at hw
    simp only [List.cons_append] at hin
    have := ih { s with pre := s.pre ++ [w], inp := ws ++ c :: rest } hs rfl
      (fun x hx => hws x (by simp [hx])) f (by simp at hf; omega)
    simp [skipchars, eof, hin, readChar, readByte, lo_ascii w hw.1, hw.2, bind, Except.bind, pure,
      Except.pure]
    exact this


/-! ### `copyline` -/

/-- `copyline(out::IO, s::IO; keep=false)`, lines 760-779: the byte loop; after a `'\r'` the
next byte is read, and if it is not `'\n'` both are written. Returns the output and the
unread input. -/
def copylineLoop (out inp : Bytes) : Bytes × Bytes :=
  match inp with
  | [] => (out, [])
  | b :: r =>
    if b = 0x0a then (out, r)
    else if b = 0x0d then
      match r with
      | [] => (out ++ [b], [])
      | b2 :: r2 => if b2 = 0x0a then (out, r2) else copylineLoop (out ++ [0x0d, b2]) r2
    else copylineLoop (out ++ [b]) r
termination_by inp.length
decreasing_by all_goals simp_all <;> omega

/-- `readline(s)` (the `IOBuffer` method of `copyline`, `base/iobuffer.jl:1010-1055`): the
bytes before the first `'\n'`, with one `'\r'` before that newline removed. -/
def readlineRef (inp : Bytes) : Bytes :=
  let line := inp.takeWhile (· != 0x0a)
  if 0x0a ∈ inp ∧ line.getLast? = some 0x0d then line.dropLast else line

/-- `copyline(out, s)` copies the same line as `readline(s)` returns, whatever the type of
`out` (its docstring: like `readline`, writing to `out`). -/
def CopylineConsistent : Prop := ∀ inp : Bytes, (copylineLoop [] inp).1 = readlineRef inp

/-- The line `"x\r\r\n"`: `copyline` writes `"x\r\r"`, `readline` gives `"x\r"`. -/
theorem copylineConsistent_refuted : ¬ CopylineConsistent := by
  intro h
  have := h [120, 13, 13, 10]
  have e : copylineLoop [] [120, 13, 13, 10] = ([120, 13, 13], []) := by
    rw [copylineLoop.eq_def]; simp
    rw [copylineLoop.eq_def]; simp
    rw [copylineLoop.eq_def]; simp
  have r : readlineRef [120, 13, 13, 10] = [120, 13] := by decide
  rw [e, r] at this
  simp at this

/-- On lines without `'\r'`, `copyline` copies the bytes before the first newline and
consumes the newline. -/
def CopylinePlain : Prop :=
  ∀ line rest : Bytes, 0x0a ∉ line → 0x0d ∉ line → ∀ out, copylineLoop out (line ++ 0x0a :: rest) = (out ++ line, rest)
theorem copylinePlain : CopylinePlain := by
  intro line rest h1 h2
  induction line with
  | nil => intro out; rw [List.nil_append, copylineLoop.eq_def]; simp
  | cons b bs ih =>
    intro out
    have hb1 : b ≠ 0x0a := fun e => h1 (e ▸ List.mem_cons_self ..)
    have hb2 : b ≠ 0x0d := fun e => h2 (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, copylineLoop.eq_def]
    simp only [hb1, hb2, ite_false]
    rw [ih (fun m => h1 (List.mem_cons_of_mem _ m)) (fun m => h2 (List.mem_cons_of_mem _ m))]
    simp

end JuliaLean.IOCov.Io
