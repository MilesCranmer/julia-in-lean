import JuliaLean.base.strings.io
import JuliaLean.Bindings.base.strings.unsafe_string
import JuliaLean.Bindings.base.iobuffer
import JuliaLean.base.iostream
import JuliaLean.base.stream
import JuliaLean.base.filesystem
import JuliaLean.base.strings.annotated_io

/-!
# `write(io, ::Union{String,SubString{String}})` for the stream types of Base

`JuliaLean.base.strings.io` models `write(::IO, ::Union{String,SubString{String}})` (`base/strings/io.jl:242-246`)
through `UnsafeWrite`, the `unsafe_write` methods of one stream type, and binds `IOBuffer` (string-IO
world), `devnull` and byte-only streams. This file binds the rest of Base: the heap-world `IOBuffer`
(`JuliaLean.Bindings.base.iobuffer.unsafeWrite`), `IOStream`, `LibuvStream`, `BufferStream`, `File`,
`AbstractPipe` (`IOContext`, `Pipe`, `Process`, `ProcessChain`), `CoreSTDOUT`/`CoreSTDERR`, and the
more specific `write(::LibuvStream, ...)`, `write(::BufferStream, ...)` and
`write(::AnnotatedIOBuffer, ...)` methods. The address of a `String` and the bytes stored there
belong to the foreign runtime that the installed `ios_write`/`uv_write`/`jl_fs_write` parameters
already represent, so `pointer` is a parameter in the stream-type worlds.
-/

namespace JuliaLean.Bindings.base.strings.io

open JuliaLean JuliaLean.base JuliaLean.base.show JuliaLean.base.strings.io


/-- The runtime places the bytes of `s` at the address `unsafe_convert(Ptr{UInt8}, s)` in the
shared byte heap of the `JuliaLean.Bindings.base.iobuffer` world. -/
def placeString {m : Type → Type} [Monad m] (heap : JuliaLean.base.iobuffer.HeapAccess m)
    (address : JuliaLean.base.pointer.U64) (s : JString) : m Unit := do
  let bytes ← heap.get
  heap.set (bytes.writeBytes address.val.toNat (s.bytes.map fun b => JInt.wrap .u8 b.toNat))

/-- `pointer(s::String)` as a typed pointer (installed `string.pointerString` over the runtime's
`unsafe_convert(Ptr{UInt8}, s)`). -/
def stringPtr (unsafeConvert : JString → Int) (s : JString) :
    JuliaLean.base.pointer.Ptr JuliaLean.base.pointer.Byte :=
  ⟨JInt.wrap .u64 (JuliaLean.base.strings.string.pointerString unsafeConvert s)⟩

def heapPointerOps (unsafeConvert : JString → Int) :
    JuliaLean.base.strings.substring.PointerOps JString where
  Pointer := JuliaLean.base.pointer.Ptr JuliaLean.base.pointer.Byte
  pointer := stringPtr unsafeConvert
  add p n := JuliaLean.base.pointer.ptrAddI64 p n

/-- `pointer(s::String)` in the heap world: the bytes of `s` are present at the address. -/
def pointerStringHeap {m : Type → Type} [Monad m]
    (heap : JuliaLean.base.iobuffer.HeapAccess m) (unsafeConvert : JString → Int) (s : JString) :
    m (JuliaLean.base.pointer.Ptr JuliaLean.base.pointer.Byte) := do
  placeString heap (stringPtr unsafeConvert s).address s
  pure (stringPtr unsafeConvert s)

/-- `pointer(x::SubString{String})` in the heap world (installed `pointerSubString`). -/
def pointerSubStringHeap {m : Type → Type} [Monad m]
    (heap : JuliaLean.base.iobuffer.HeapAccess m) (unsafeConvert : JString → Int)
    (x : JuliaLean.base.strings.substring.SubString JString) :
    m (JuliaLean.base.pointer.Ptr JuliaLean.base.pointer.Byte) := do
  placeString heap (stringPtr unsafeConvert x.string).address x.string
  pure (JuliaLean.base.strings.substring.pointerSubString (heapPointerOps unsafeConvert) x)

/-! ## 4. The heap world of `JuliaLean.Bindings.base.iobuffer` -/

open JuliaLean.Bindings.base.iobuffer in
/-- `unsafe_write(to::GenericIOBuffer, p::Ptr{UInt8}, nb::UInt; cancel)` of an `IOBuffer` whose data
is a represented byte vector: the installed `unsafeWrite` of the `_unsafe_write` dispatch
(iobuffer.jl:902-946), with `cancel = nothing` as `CancelTokenArg.none` and a token as
`CancelTokenArg.token`. `io` is the buffer's reference. -/
def heapUnsafeWrite {E Ref Data NewData Source Task Scope : Type} [UnsafeWriteDispatch Data]
    (access : JuliaLean.base.iobuffer.Access (RuntimeM E (ArrayWorld Ref Data)) Ref Data)
    (storage : JuliaLean.base.iobuffer.Storage (RuntimeM E (ArrayWorld Ref Data)) Ref Data NewData)
    (scopeOps : JuliaLean.base.cancellation.ScopeOps (ArrayWorld Ref Data) Source Task Scope)
    (tokenOps : JuliaLean.base.cancellation.TokenOps (ArrayWorld Ref Data) Source)
    (slow : Task → JuliaLean.base.cancellation.M (ArrayWorld Ref Data)
      (Option (JuliaLean.base.cancellation.CancellationToken Source)))
    (handleCancellation : Option Source → JuliaLean.base.cancellation.U8 →
      JuliaLean.base.cancellation.M (ArrayWorld Ref Data) Unit)
    (heap : JuliaLean.base.iobuffer.HeapAccess (RuntimeM E (ArrayWorld Ref Data))) :
    UnsafeWrite (RuntimeM E (ArrayWorld Ref Data)) Ref
      (JuliaLean.base.pointer.Ptr JuliaLean.base.pointer.Byte)
      (JuliaLean.base.cancellation.CancellationToken Source) I where
  plain ref p n := unsafeWrite access storage scopeOps tokenOps slow handleCancellation heap
    ref p n .useDefault
  explicit ref p n token := unsafeWrite access storage scopeOps tokenOps slow handleCancellation
    heap ref p n (match token with
      | none => .none
      | some token => .token token)
  toInt := JuliaLean.base.int.remT .i64

open JuliaLean.Bindings.base.iobuffer in
/-- `write(io::IOBuffer, s::String)` in the heap world. -/
def writeStringHeap {E Ref Data NewData Source Task Scope : Type} [UnsafeWriteDispatch Data]
    (access : JuliaLean.base.iobuffer.Access (RuntimeM E (ArrayWorld Ref Data)) Ref Data)
    (storage : JuliaLean.base.iobuffer.Storage (RuntimeM E (ArrayWorld Ref Data)) Ref Data NewData)
    (scopeOps : JuliaLean.base.cancellation.ScopeOps (ArrayWorld Ref Data) Source Task Scope)
    (tokenOps : JuliaLean.base.cancellation.TokenOps (ArrayWorld Ref Data) Source)
    (slow : Task → JuliaLean.base.cancellation.M (ArrayWorld Ref Data)
      (Option (JuliaLean.base.cancellation.CancellationToken Source)))
    (handleCancellation : Option Source → JuliaLean.base.cancellation.U8 →
      JuliaLean.base.cancellation.M (ArrayWorld Ref Data) Unit)
    (heap : JuliaLean.base.iobuffer.HeapAccess (RuntimeM E (ArrayWorld Ref Data)))
    (unsafeConvert : JString → Int) (ref : Ref) (s : JString)
    (cancel : JuliaLean.base.io.CancelArg (JuliaLean.base.cancellation.CancellationToken Source)) :
    RuntimeM E (ArrayWorld Ref Data) JInt64 :=
  writeConcreteString
    (heapUnsafeWrite access storage scopeOps tokenOps slow handleCancellation heap)
    (pointerStringHeap heap unsafeConvert) sizeofJString ref s cancel

open JuliaLean.Bindings.base.iobuffer in
/-- `write(io::IOBuffer, s::SubString{String})` in the heap world. -/
def writeSubStringHeap {E Ref Data NewData Source Task Scope : Type} [UnsafeWriteDispatch Data]
    (access : JuliaLean.base.iobuffer.Access (RuntimeM E (ArrayWorld Ref Data)) Ref Data)
    (storage : JuliaLean.base.iobuffer.Storage (RuntimeM E (ArrayWorld Ref Data)) Ref Data NewData)
    (scopeOps : JuliaLean.base.cancellation.ScopeOps (ArrayWorld Ref Data) Source Task Scope)
    (tokenOps : JuliaLean.base.cancellation.TokenOps (ArrayWorld Ref Data) Source)
    (slow : Task → JuliaLean.base.cancellation.M (ArrayWorld Ref Data)
      (Option (JuliaLean.base.cancellation.CancellationToken Source)))
    (handleCancellation : Option Source → JuliaLean.base.cancellation.U8 →
      JuliaLean.base.cancellation.M (ArrayWorld Ref Data) Unit)
    (heap : JuliaLean.base.iobuffer.HeapAccess (RuntimeM E (ArrayWorld Ref Data)))
    (unsafeConvert : JString → Int) (ref : Ref)
    (s : JuliaLean.base.strings.substring.SubString JString)
    (cancel : JuliaLean.base.io.CancelArg (JuliaLean.base.cancellation.CancellationToken Source)) :
    RuntimeM E (ArrayWorld Ref Data) JInt64 :=
  writeConcreteString
    (heapUnsafeWrite access storage scopeOps tokenOps slow handleCancellation heap)
    (pointerSubStringHeap heap unsafeConvert) sizeofJSubString ref s cancel

/-! ## 5. The other Base IO kinds (world `JuliaLean.base.io.M World`)

`IOStream`, `LibuvStream` (`PipeEndpoint`, `TTY`, `BufferStream`), `Pipe`, `Process`, `ProcessChain`,
`AnnotatedIOBuffer`, `File`, `CoreSTDOUT`/`CoreSTDERR` and `SecretBuffer` use the installed models of
`base/iostream.lean`, `base/stream.lean`, `base/filesystem.lean`, `base/coreio.lean`, `base/io.lean`
and `base/strings/annotated_io.lean`, all in the mutable world `io.M World`. The address of a `String` and
the bytes stored there belong to the foreign runtime these models already take as a parameter
(`ios_write`, `uv_write`, `jl_fs_write`), so `pointer` is the runtime's `pointer(s)` (named gap
`stream-world-string-pointer`). -/

section IOWorld

open JuliaLean.base.io (M CancelArg)

/-- `unsafe_write(s::IOStream, p, nb; cancel)` (iostream.jl:416-426), installed `iostream.unsafeWrite`. -/
def iostreamUnsafeWrite {World Stream Vector Lock Token : Type}
    (access : JuliaLean.base.iostream.Access World Stream Vector Lock)
    (locks : JuliaLean.base.iostream.Locks World Lock)
    (runtime : JuliaLean.base.iostream.Runtime World Vector)
    (precheck : CancelArg Token → M World (CancelArg Token)) :
    UnsafeWrite (M World) Stream JuliaLean.base.stream.BytePointer Token JuliaLean.base.io.I where
  plain s p n := JuliaLean.base.iostream.unsafeWrite access locks runtime precheck s p n .default
  explicit s p n token :=
    JuliaLean.base.iostream.unsafeWrite access locks runtime precheck s p n (.explicit token)
  toInt := JuliaLean.base.int.remT .i64

/-- `unsafe_write(s::LibuvStream, p, n; cancel)` (stream.jl:1736-1739), installed `stream.unsafeWrite`
over the installed `_unsafe_write_owned` (`writeOwned`, stream.jl:1741-1772). -/
def libuvUnsafeWrite {World Stream Owner Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (writeOwned : Stream → JuliaLean.base.stream.BytePointer → JuliaLean.base.io.U →
      CancelArg Token → Option Owner → Bool → M World JuliaLean.base.io.I) :
    UnsafeWrite (M World) Stream JuliaLean.base.stream.BytePointer Token JuliaLean.base.io.I where
  plain s p n := JuliaLean.base.stream.unsafeWrite precheck writeOwned s p n .default
  explicit s p n token := JuliaLean.base.stream.unsafeWrite precheck writeOwned s p n (.explicit token)
  toInt := JuliaLean.base.int.remT .i64

/-- `unsafe_write(s::BufferStream, p, nb; cancel)` (stream.jl:2404-2414), installed
`stream.bufferUnsafeWrite`. -/
def bufferStreamUnsafeWrite {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : JuliaLean.base.stream.Access World Stream
      (JuliaLean.base.stream.BufferFields Buffer Condition Lock))
    (buffers : JuliaLean.base.stream.BufferOps World Buffer Vector Data)
    (ops : JuliaLean.base.stream.ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (checkOpen : Stream → M World Unit) :
    UnsafeWrite (M World) Stream JuliaLean.base.stream.BytePointer Token JuliaLean.base.io.I where
  plain s p n :=
    JuliaLean.base.stream.bufferUnsafeWrite access buffers ops precheck checkOpen s p n .default
  explicit s p n token :=
    JuliaLean.base.stream.bufferUnsafeWrite access buffers ops precheck checkOpen s p n
      (.explicit token)
  toInt := JuliaLean.base.int.remT .i64

/-- `unsafe_write(f::File, buf::Ptr{UInt8}, len::UInt, offset::Int64=Int64(-1))` (filesystem.jl:324-330),
installed `filesystem.unsafeWriteDefault` (offset `-1`). The method has no `cancel` keyword, so an
explicit token is a `MethodError`; its `len::UInt` result is reduced by `% Int`. -/
def fileUnsafeWrite {World Object Handle RawFD Req CString Ptr Buffer RefByte Overlapped Regex Stat
    Token : Type}
    (ops : JuliaLean.base.filesystem.FileSystemOps World Object Handle RawFD Req CString Ptr Buffer
      RefByte Overlapped Regex Stat) :
    UnsafeWrite (M World) (JuliaLean.base.filesystem.File Object) Ptr Token
      JuliaLean.base.filesystem.U64 where
  plain f p n := JuliaLean.base.filesystem.unsafeWriteDefault ops f p n
  explicit _ _ _ _ := throw (.jl (.methodError "unsafe_write"))
  toInt := JuliaLean.base.int.remT .i64

/-- `unsafe_write(s::IO, p::Ptr{UInt8}, n::UInt)` (io.jl:358-364), installed `io.unsafeWrite`, for any
stream type that defines only `write(::T, ::UInt8)` (`SecretBuffer`, user types); `writeByte` is that
method. No `cancel` keyword. -/
def fallbackUnsafeWriteIO {World Stream Pointer Token : Type}
    (ops : JuliaLean.base.io.Ops World Stream)
    (load : Pointer → JuliaLean.base.io.U → M World JuliaLean.base.io.Byte) :
    UnsafeWrite (M World) Stream Pointer Token JuliaLean.base.io.I where
  plain s p n := JuliaLean.base.io.unsafeWrite ops load s p n
  explicit _ _ _ _ := throw (.jl (.methodError "unsafe_write"))
  toInt := JuliaLean.base.int.remT .i64

/-- `unsafe_write(io::AbstractPipe, p, nb; cancel)` (io.jl:503-505), installed `io.pipeUnsafeWrite`:
`IOContext`, `Pipe`, `Process`, `ProcessChain` and any other `AbstractPipe` forward to the method of
`pipe_writer(io)`, with the token when one was passed. -/
def pipeUnsafeWrite {World Pipe Stream Pointer Token N : Type}
    (writer : Pipe → M World Stream) (w : UnsafeWrite (M World) Stream Pointer Token N) :
    UnsafeWrite (M World) Pipe Pointer Token N where
  plain pipe p n :=
    JuliaLean.base.io.pipeUnsafeWrite writer (fun s p n => w.plain s p n)
      (fun s p n token => w.explicit s p n token) pipe p n .default
  explicit pipe p n token :=
    JuliaLean.base.io.pipeUnsafeWrite writer (fun s p n => w.plain s p n)
      (fun s p n token => w.explicit s p n token) pipe p n (.explicit token)
  toInt := w.toInt

/-- `unsafe_write(io::CoreIO, x::Ptr{UInt8}, nb::UInt) = Core.unsafe_write(io, x, nb)` (coreio.jl:31) for
`Core.CoreSTDOUT`/`Core.CoreSTDERR`. `Core.unsafe_write` (boot.jl:984, `jl_uv_puts`) returns the `UInt`
`nb`; the installed `coreio.unsafeWriteCoreIO` types its result as `Int`, so the adapter passed to it
applies the `% Int` of `write` to that `UInt` and `toInt` is the identity. No `cancel` keyword. -/
def coreStdUnsafeWrite {ε Pointer Token : Type} (methodError : ε)
    (coreUnsafeWrite : JuliaLean.base.coreio.CoreStdIO → Pointer → JInt .u64 →
      Except ε (JInt .u64)) :
    UnsafeWrite (Except ε) JuliaLean.base.coreio.CoreStdIO Pointer Token JInt64 where
  plain io p n := JuliaLean.base.coreio.unsafeWriteCoreIO
    (fun io p n => (fun written => JuliaLean.base.int.remT .i64 written) <$> coreUnsafeWrite io p n)
    io p n
  explicit _ _ _ _ := throw methodError
  toInt := fun written => written

/-! ### The `write(io, ::Union{String,SubString{String}})` methods that are not io.jl:242 -/

/--
Julia source: base/stream.jl:1691-1697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::LibuvStream, str::Union{String, SubString{String}};
               cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    GC.@preserve str begin
        return Int(_unsafe_write_owned(s, pointer(str), UInt(sizeof(str)), cancel, str, false))
    end
end
```
More specific than io.jl:242 for every `LibuvStream` (`PipeEndpoint`, `TTY`; the `BufferStream` method
below is more specific still): installed `stream.writeOwnedString` over the installed
`_unsafe_write_owned`, owner `str`. -/
def writeStringLibuv {World Stream A Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World JuliaLean.base.stream.BytePointer) (sizeof : A → JInt64)
    (writeOwned : Stream → JuliaLean.base.stream.BytePointer → JuliaLean.base.io.U →
      CancelArg Token → Option A → Bool → M World JuliaLean.base.io.I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World JuliaLean.base.io.I :=
  JuliaLean.base.stream.writeOwnedString precheck pointer (fun a => pure (sizeof a)) writeOwned
    stream value cancel

/--
Julia source: base/stream.jl:2388-2394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::BufferStream, str::Union{String, SubString{String}};
               cancel::CancelTokenArg=DEFAULT_CANCEL)
    precheck_cancel_arg(cancel)
    GC.@preserve str begin
        return Int(unsafe_write(s, pointer(str), UInt(sizeof(str))))
    end
end
```
Installed `stream.bufferWriteString`; its `unsafe_write` is the `BufferStream` method above (plain call). -/
def writeStringBufferStream {World Stream Buffer Condition Lock Vector Data A Token : Type}
    (access : JuliaLean.base.stream.Access World Stream
      (JuliaLean.base.stream.BufferFields Buffer Condition Lock))
    (buffers : JuliaLean.base.stream.BufferOps World Buffer Vector Data)
    (ops : JuliaLean.base.stream.ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (checkOpen : Stream → M World Unit)
    (pointer : A → M World JuliaLean.base.stream.BytePointer) (sizeof : A → JInt64)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World JuliaLean.base.io.I :=
  JuliaLean.base.stream.bufferWriteString precheck pointer (fun a => pure (sizeof a))
    (fun s p n => (bufferStreamUnsafeWrite access buffers ops precheck checkOpen).plain s p n)
    stream value cancel

/-- io.jl:242 on a stream type without its own `write(::T, ::Union{String,SubString{String}})` method
(`IOStream`, `File`, `SecretBuffer`, `Pipe`, `Process`, `ProcessChain`, `IOContext`): the stream's
`unsafe_write` instance in the world `io.M World`. -/
def writeStringIOWorld {World Io P Token A : Type}
    (w : UnsafeWrite (M World) Io P Token JuliaLean.base.io.I) (pointer : A → M World P)
    (sizeof : A → JInt64) (io : Io) (s : A) (cancel : CancelArg Token) :
    M World JuliaLean.base.io.I :=
  writeConcreteString w pointer sizeof io s cancel

/--
Julia source: base/strings/annotated_io.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::AnnotatedIOBuffer, s::Union{SubString{String}, String}) = write(io.io, s)
```
Installed `annotated_io.writePlainString` for a call without `cancel`; `write(io.io, s)` is io.jl:242
on the inner `IOBuffer`. A call with `cancel=` is dispatched to io.jl:242 itself, because only methods
that accept the keyword take part in a keyword call, so `AnnotatedIOBuffer <: AbstractPipe` forwards
`unsafe_write(...; cancel)` to `io.io` (`pipeUnsafeWrite`). -/
def writeStringAnnotatedIOBuffer {World Buffer Regions A P Token : Type}
    (w : UnsafeWrite (M World) Buffer P Token JuliaLean.base.io.I) (pointer : A → M World P)
    (sizeof : A → JInt64)
    (io : JuliaLean.base.strings.annotated_io.AnnotatedIOBuffer Buffer Regions) (s : A) :
    CancelArg Token → M World JuliaLean.base.io.I
  | .default =>
    JuliaLean.base.strings.annotated_io.writePlainString
      (fun buffer s => writeStringIOWorld w pointer sizeof buffer s .default) io s
  | .explicit token =>
    writeStringIOWorld (pipeUnsafeWrite (fun io => pure io.io) w) pointer sizeof io s
      (.explicit token)

end IOWorld

end JuliaLean.Bindings.base.strings.io
