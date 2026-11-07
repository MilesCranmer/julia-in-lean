import JuliaLean.base.locks_mt
import JuliaLean.base.io
import JuliaLean.base.coreio
import JuliaLean.base.iobuffer
import JuliaLean.base.iostream
import JuliaLean.base.int
import JuliaLean.base.pointer

import JuliaLean.base.libuv
/-!
# Model of `base/stream.jl`

Typed libuv, pipe and BufferStream methods at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Handles, buffers, locks and
conditions are references into the same mutable world as generic IO. Foreign
calls and scheduler operations are typed parameters with no assumed laws.
Exceptions retain mutations and lock state. Fuel-free waits retain divergence.
BufferStream has separate fields because it has no libuv handle or send buffer.
Request waits preserve ownership, cancellation severity and detached-buffer roots.
-/

namespace JuliaLean.base.stream

open JuliaLean
open JuliaLean.base.io (I U Byte M Error CancelArg Cancellation SymbolName)

abbrev Handle := JuliaLean.base.pointer.Ptr Unit
abbrev BytePointer := JuliaLean.base.pointer.Ptr Byte
abbrev CInt := JInt .i32

def i := JuliaLean.base.io.i
def u := JuliaLean.base.io.u
def cint (value : Int) : CInt := JInt.wrap .i32 value

def nullHandle : Handle := ⟨u 0⟩

structure Access (World Ref Fields : Type) where
  get : Ref → M World Fields
  set : Ref → Fields → M World Unit
  new : Fields → M World Ref

structure UVFields (Buffer Condition Lock : Type) where
  handle : Handle
  status : I
  buffer : Buffer
  condition : Condition
  readerror : Option Error
  sendbuf : Option Buffer
  mutex : Lock
  throttle : I

structure Metadata (World Ref Condition : Type) where
  handle : Ref → M World Handle
  status : Ref → M World I
  setHandle : Ref → Handle → M World Unit
  setStatus : Ref → I → M World Unit
  condition : Ref → M World Condition

structure BufferFields (Buffer Condition Lock : Type) where
  buffer : Buffer
  condition : Condition
  readerror : Option Error
  bufferWrites : Bool
  mutex : Lock
  status : I

structure ConditionOps (World Condition Token : Type) where
  lock : Condition → M World Unit
  unlock : Condition → M World Unit
  wait : Condition → Option Token → M World Unit
  notify : Condition → M World Unit

structure Pipe (Endpoint : Type) where
  input : Endpoint
  output : Endpoint

structure RedirectStdStream where
  unixFD : I
  writable : Bool

/-- Base.lock(f, lock) releases the captured lock even when f throws. -/
def withLock {World Lock A : Type} (lock unlock : Lock → M World Unit)
    (mutex : Lock) (action : M World A) : M World A := do
  lock mutex
  JuliaLean.base.io.finallyDo action (unlock mutex)

def capture {World A : Type} (action : M World A) : M World (Except Error A) :=
  tryCatch (do pure (.ok (← action))) (fun error => pure (.error error))

def rethrowResult {World A : Type} : Except Error A → M World A
  | .ok value => pure value
  | .error error => throw error

/-- A successful condition wait reacquires its lock; a throwing wait drops
this frame's lock level. The returned flag mirrors the source's `locked` local. -/
def conditionWaitLoop {World : Type} (condition : M World Bool) (wait : M World Unit) :
    M World (Bool × Except Error Unit) :=
  JuliaLean.base.io.whileLoop (fun _ : Unit => do
    match ← capture condition with
    | .error error => pure (.inl (true, .error error))
    | .ok false => pure (.inl (true, .ok ()))
    | .ok true =>
      match ← capture wait with
      | .error error => pure (.inl (false, .error error))
      | .ok () => pure (.inr ())) ()

inductive ShowArg (Kind FD : Type) where
  | kind (value : Kind)
  | descriptor (value : FD)
  | text (value : String)
  | count (value : I)
  | boolean (value : Bool)

structure BufferOps (World Buffer Vector Data : Type) where
  fields : JuliaLean.base.iobuffer.Access (M World) Buffer Data
  available : Buffer → M World I
  readByte : Buffer → M World Byte
  take : Buffer → M World Vector
  readuntil : Buffer → Byte → Bool → M World Vector
  occursin : Byte → Buffer → M World Bool
  unsafeRead : Buffer → BytePointer → U → M World Unit
  unsafeWrite : Buffer → BytePointer → U → M World I
  readbytes : Buffer → Vector → I → M World I

inductive RedirectArg (Path Stream : Type) where
  | unchanged
  | path (value : Path)
  | stream (value : Stream)

inductive Resolution (Stream : Type) where
  | unchanged
  | borrowed (value : Option Stream) (previous : Stream)
  | owned (value previous : Stream)

def Resolution.current {Stream : Type} : Resolution Stream → Option Stream
  | .unchanged => none
  | .borrowed value _ => value
  | .owned value _ => some value

def Resolution.previous {Stream : Type} : Resolution Stream → Option Stream
  | .unchanged => none
  | .borrowed _ old | .owned _ old => some old

def closeResolution {World Stream : Type} (close : Stream → M World Unit) : Resolution Stream → M World Unit
  | .owned value _ => close value
  | .borrowed _ _ | .unchanged => pure ()

structure StdioOps (World IO OSHandle RawFD Module Condition : Type) where
  beginIO : M World Unit
  endIO : M World Unit
  handleType : Handle → M World CInt
  guessHandle : OSHandle → M World CInt
  fileType : CInt
  ttyType : CInt
  tcpType : CInt
  pipeType : CInt
  fileHandle : Handle → M World OSHandle
  openOSHandle : OSHandle → CInt → M World RawFD
  convertOSFD : OSHandle → M World CInt
  convertRawFD : RawFD → M World CInt
  fdio : CInt → M World IO
  ttyHandle : Handle → I → M World IO
  ttyFD : OSHandle → M World IO
  pipeHandle : Handle → I → M World IO
  pipeFD : OSHandle → M World IO
  requireStdlib : U → U → String → M World Module
  tcpHandle : Module → Handle → I → M World IO
  tcpFD : Module → OSHandle → M World IO
  metadata : Metadata World IO Condition
  isPty : Handle → M World CInt
  formatType : CInt → String

structure TTYSizeOps (World IO Command Process Input Pieces Parsed Ref : Type) where
  checkOpen : IO → M World Unit
  defaultSize : M World (I × I)
  isPty : IO → M World Bool
  command : List String → M World Command
  openProcess : Command → String → IO → M World Process
  processOutput : Process → M World Input
  readString : Input → M World String
  split : String → M World Pieces
  parseInts : Pieces → M World Parsed
  firstTwo : Parsed → M World (I × I)
  newRef : CInt → M World Ref
  readRef : Ref → M World CInt
  beginIO : M World Unit
  endIO : M World Unit
  getWinSize : IO → Ref → Ref → M World CInt

structure UvReqWait (Witness Owner : Type) where
  request : Handle
  witness : Witness
  owner : Option Owner
  trycancel : Bool

inductive RequestWaitable (Witness Owner Source : Type) where
  | request (value : UvReqWait Witness Owner)
  | source (value : Source) (floor : Byte)

structure RequestOps (World Task Entry Source Witness Owner Queue Result : Type) where
  currentTask : M World Task
  cachedEntry : Task → M World Entry
  cancelEntry : Task → Source → Byte → M World Entry
  arm : Task → Entry → M World Unit
  setWitness : Entry → Witness → M World Unit
  clearWitness : Entry → Witness → M World Unit
  clearUVWitness : Entry → M World Unit
  preserve : Task → M World Unit
  unpreserve : Task → M World Unit
  sigatomicBegin : M World Unit
  sigatomicEnd : M World Unit
  beginIO : M World Unit
  endIO : M World Unit
  data : Handle → M World Handle
  setData : Handle → Handle → M World Unit
  cancel : Handle → M World CInt
  free : Handle → M World Unit
  rootDetached : Handle → Option Owner → M World Unit
  unrootDetached : Handle → M World Unit
  entryPointer : Entry → M World Handle
  pointerEntry : Handle → M World Entry
  entryTask : JuliaLean.base.locks_mt.MemoryOrder → Entry → M World (Option Task)
  claim : Task → Entry → M World Bool
  replaceWaiting : JuliaLean.base.locks_mt.MemoryOrder → JuliaLean.base.locks_mt.MemoryOrder →
    Task → Option Entry → Option Entry → M World (Option Entry × Bool)
  queue : Task → M World (Option Queue)
  deleteFirst : Queue → Task → M World Unit
  park : List (RequestWaitable Witness Owner Source) → Entry → Bool → M World Bool
  withdraw : List (RequestWaitable Witness Owner Source) → Entry → Byte → M World Unit
  waitSafe : List (RequestWaitable Witness Owner Source) → Entry → M World Result
  checkCancel : Option Source → M World Unit
  wakeValue : Byte
  wakeFired : Byte
  wakeInterrupted : Byte
  wakeWithdrawn : Byte

-- UNTRANSLATED
-- Source: base/stream.jl:1-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- import .Libc: RawFD, dup
-- if Sys.iswindows()
--     import .Libc: WindowsRawSocket
--     const OS_HANDLE = WindowsRawSocket
--     const INVALID_OS_HANDLE = WindowsRawSocket(Ptr{Cvoid}(-1))
-- else
--     const OS_HANDLE = RawFD
--     const INVALID_OS_HANDLE = RawFD(-1)
-- end
-- 
-- 
-- ## types ##
-- abstract type IOServer end
-- """
--     LibuvServer
-- 
-- An abstract type for IOServers handled by libuv.
-- 
-- If `server isa LibuvServer`, it must obey the following interface:
-- 
-- - `server.handle` must be a `Ptr{Cvoid}`
-- - `server.status` must be an `Int`
-- - `server.cond` must be a `GenericCondition`
-- """
-- abstract type LibuvServer <: IOServer end
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:29-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getproperty(server::LibuvServer, name::Symbol)
    if name === :handle
        return getfield(server, :handle)::Ptr{Cvoid}
    elseif name === :status
        return getfield(server, :status)::Int
    elseif name === :cond
        return getfield(server, :cond)::GenericCondition
    else
        return getfield(server, name)
    end
end
```
-/
def serverGetproperty {World Server Field : Type}
    (getfield : Server → SymbolName → M World Field)
    (assertHandle assertInt assertCondition : Field → M World Field)
    (server : Server) (name : SymbolName) : M World Field := do
  if name.value == "handle" then assertHandle (← getfield server ⟨"handle"⟩)
  else if name.value == "status" then assertInt (← getfield server ⟨"status"⟩)
  else if name.value == "cond" then assertCondition (← getfield server ⟨"cond"⟩)
  else getfield server name

-- UNTRANSLATED
-- Source: base/stream.jl:40-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     LibuvStream
-- 
-- An abstract type for IO streams handled by libuv.
-- 
-- If `stream isa LibuvStream`, it must obey the following interface:
-- 
-- - `stream.handle`, if present, must be a `Ptr{Cvoid}`
-- - `stream.status`, if present, must be an `Int`
-- - `stream.buffer`, if present, must be an `IOBuffer`
-- - `stream.sendbuf`, if present, must be a `Union{Nothing,IOBuffer}`
-- - `stream.cond`, if present, must be a `GenericCondition`
-- - `stream.lock`, if present, must be an `AbstractLock`
-- - `stream.throttle`, if present, must be an `Int`
-- """
-- abstract type LibuvStream <: IO end
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:58-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getproperty(stream::LibuvStream, name::Symbol)
    if name === :handle
        return getfield(stream, :handle)::Ptr{Cvoid}
    elseif name === :status
        return getfield(stream, :status)::Int
    elseif name === :buffer
        return getfield(stream, :buffer)::IOBuffer
    elseif name === :sendbuf
        return getfield(stream, :sendbuf)::Union{Nothing,IOBuffer}
    elseif name === :cond
        return getfield(stream, :cond)::GenericCondition
    elseif name === :lock
        return getfield(stream, :lock)::AbstractLock
    elseif name === :throttle
        return getfield(stream, :throttle)::Int
    else
        return getfield(stream, name)
    end
end
```
-/
def streamGetproperty {World Stream Field : Type}
    (getfield : Stream → SymbolName → M World Field)
    (assertHandle assertInt assertBuffer assertOptionalBuffer assertCondition assertLock : Field → M World Field)
    (stream : Stream) (name : SymbolName) : M World Field := do
  if name.value == "handle" then assertHandle (← getfield stream ⟨"handle"⟩)
  else if name.value == "status" then assertInt (← getfield stream ⟨"status"⟩)
  else if name.value == "buffer" then assertBuffer (← getfield stream ⟨"buffer"⟩)
  else if name.value == "sendbuf" then assertOptionalBuffer (← getfield stream ⟨"sendbuf"⟩)
  else if name.value == "cond" then assertCondition (← getfield stream ⟨"cond"⟩)
  else if name.value == "lock" then assertLock (← getfield stream ⟨"lock"⟩)
  else if name.value == "throttle" then assertInt (← getfield stream ⟨"throttle"⟩)
  else getfield stream name

-- UNTRANSLATED
-- Source: base/stream.jl:77-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # IO
-- # +- GenericIOBuffer{T<:AbstractVector{UInt8}} (not exported)
-- # +- AbstractPipe (not exported)
-- # .  +- Pipe
-- # .  +- Process (not exported)
-- # .  +- ProcessChain (not exported)
-- # +- DevNull (not exported)
-- # +- Filesystem.File
-- # +- LibuvStream (not exported)
-- # .  +- PipeEndpoint (not exported)
-- # .  +- TCPSocket
-- # .  +- TTY (not exported)
-- # .  +- UDPSocket
-- # .  +- BufferStream (FIXME: 2.0)
-- # +- IOBuffer = Base.GenericIOBuffer{Vector{UInt8}}
-- # +- IOStream
-- 
-- # IOServer
-- # +- LibuvServer
-- # .  +- PipeServer
-- # .  +- TCPServer
-- 
-- # Redirectable = Union{IO, FileRedirect, Libc.RawFD} (not exported)
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bytesavailable(s::LibuvStream) = bytesavailable(s.buffer)::Int
```
-/
def bytesavailable {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (available : Buffer → M World I) (stream : Stream) : M World I := do
  available (← access.get stream).buffer

-- UNTRANSLATED
-- Source: base/stream.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:104-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eof(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    bytesavailable(s) > 0 && return false
    wait_readnb(s, 1, resolve_cancel_token(cancel))
    # This function is race-y if used from multiple threads, but we guarantee
    # it to never return true until the stream is definitively exhausted
    # and that we won't return true if there's a readerror pending (it'll instead get thrown).
    # This requires some careful ordering here (TODO: atomic loads)
    bytesavailable(s) > 0 && return false
    open = isreadable(s) # must precede readerror check
    s.readerror === nothing || throw(s.readerror)
    return !open
end
```
-/
def eof {World Stream Buffer Condition Lock Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (available : Stream → M World I) (waitRead : Stream → I → Option Token → M World Unit)
    (readable : Stream → M World Bool) (stream : Stream) (cancel : CancelArg Token) : M World Bool := do
  let cancel ← precheck cancel
  if (← available stream).val > 0 then return false
  waitRead stream (i 1) (← resolve cancel)
  if (← available stream).val > 0 then return false
  let readable ← readable stream
  match (← access.get stream).readerror with
  | some error => throw error
  | none => pure (!readable)

-- UNTRANSLATED
-- Source: base/stream.jl:117-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Limit our default maximum read and buffer size,
-- # to avoid DoS-ing ourself into an OOM situation
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const DEFAULT_READ_BUFFER_SZ = 10485760 # 10 MB
```
-/
def defaultReadBufferSize : I := i 10485760

-- UNTRANSLATED
-- Source: base/stream.jl:121-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # manually limit our write size, if the OS doesn't support full-size writes
-- if Sys.iswindows()
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:124-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    const MAX_OS_WRITE = UInt(0x1FF0_0000) # 511 MB (determined semi-empirically, limited to 31 MB on XP)
else
    const MAX_OS_WRITE = UInt(0x7FFF_0000) # almost 2 GB (both macOS and linux have this kernel restriction, although only macOS documents it)
end

```
-/
def maxOSWrite (windows : Bool) : U := u (if windows then 0x1ff00000 else 0x7fff0000)

-- UNTRANSLATED
-- Source: base/stream.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusUninit      = 0 # handle is allocated, but not initialized
```
-/
def statusUninit : I := i 0

/--
Julia source: base/stream.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusInit        = 1 # handle is valid, but not connected/active
```
-/
def statusInit : I := i 1

/--
Julia source: base/stream.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusConnecting  = 2 # handle is in process of connecting
```
-/
def statusConnecting : I := i 2

/--
Julia source: base/stream.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusOpen        = 3 # handle is usable
```
-/
def statusOpen : I := i 3

/--
Julia source: base/stream.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusActive      = 4 # handle is listening for read/write/connect events
```
-/
def statusActive : I := i 4

/--
Julia source: base/stream.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusClosing     = 5 # handle is closing / being closed
```
-/
def statusClosing : I := i 5

/--
Julia source: base/stream.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusClosed      = 6 # handle is closed
```
-/
def statusClosed : I := i 6

/--
Julia source: base/stream.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusEOF         = 7 # handle is a TTY that has seen an EOF event (pretends to be closed until reseteof is called)
```
-/
def statusEOF : I := i 7

/--
Julia source: base/stream.jl:138-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const StatusPaused      = 8 # handle is Active, but not consuming events, and will transition to Open if it receives an event
```
-/
def statusPaused : I := i 8

/--
Julia source: base/stream.jl:139-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_status_string(x)
    s = x.status
    if x.handle == C_NULL
        if s == StatusClosed
            return "closed"
        elseif s == StatusUninit
            return "null"
        end
        return "invalid status"
    elseif s == StatusUninit
        return "uninit"
    elseif s == StatusInit
        return "init"
    elseif s == StatusConnecting
        return "connecting"
    elseif s == StatusOpen
        return "open"
    elseif s == StatusActive
        return "active"
    elseif s == StatusPaused
        return "paused"
    elseif s == StatusClosing
        return "closing"
    elseif s == StatusClosed
        return "closed"
    elseif s == StatusEOF
        return "eof"
    end
    return "invalid status"
end
```
-/
def statusString {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (reference : Ref) : M World String := do
  let status ← metadata.status reference
  if (← metadata.handle reference).address.val = 0 then
    if status.val = 6 then return "closed"
    else if status.val = 0 then return "null"
    else return "invalid status"
  else if status.val = 0 then return "uninit"
  else if status.val = 1 then return "init"
  else if status.val = 2 then return "connecting"
  else if status.val = 3 then return "open"
  else if status.val = 4 then return "active"
  else if status.val = 8 then return "paused"
  else if status.val = 5 then return "closing"
  else if status.val = 6 then return "closed"
  else if status.val = 7 then return "eof"
  else return "invalid status"

-- UNTRANSLATED
-- Source: base/stream.jl:169-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- mutable struct PipeEndpoint <: LibuvStream
--     handle::Ptr{Cvoid}
--     status::Int
--     buffer::IOBuffer
--     cond::ThreadSynchronizer
--     readerror::Any
--     sendbuf::Union{IOBuffer, Nothing}
--     lock::ReentrantLock # advisory lock
--     throttle::Int
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:179-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function PipeEndpoint(handle::Ptr{Cvoid}, status)
        p = new(handle,
                status,
                PipeBuffer(),
                ThreadSynchronizer(),
                nothing,
                nothing,
                ReentrantLock(),
                DEFAULT_READ_BUFFER_SZ)
        associate_julia_struct(handle, p)
        finalizer(uvfinalize, p)
        return p
    end
```
-/
def pipeEndpointFromHandle {World Stream Buffer Condition Lock Status : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (toStatus : Status → M World I) (pipeBuffer : M World Buffer)
    (newCondition : M World Condition) (newLock : M World Lock)
    (associate : Handle → Stream → M World Unit) (finalize : Stream → M World Unit)
    (handle : Handle) (status : Status) : M World Stream := do
  let status ← toStatus status
  let buffer ← pipeBuffer
  let condition ← newCondition
  let mutex ← newLock
  let stream ← access.new ⟨handle, status, buffer, condition, none, none, mutex, defaultReadBufferSize⟩
  associate handle stream
  finalize stream
  pure stream

-- UNTRANSLATED
-- Source: base/stream.jl:192-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:194-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function PipeEndpoint()
    pipe = PipeEndpoint(Libc.malloc(_sizeof_uv_named_pipe), StatusUninit)
    iolock_begin()
    err = ccall(:uv_pipe_init, Cint, (Ptr{Cvoid}, Ptr{Cvoid}, Cint), eventloop(), pipe.handle, 0)
    uv_error("failed to create pipe endpoint", err)
    pipe.status = StatusInit
    iolock_end()
    return pipe
end
```
-/
def pipeEndpoint {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (allocate : M World Handle) (construct : Handle → I → M World Stream)
    (beginIO endIO : M World Unit) (eventloop : M World Handle)
    (initializeNative : Handle → Handle → CInt → M World CInt)
    (uvError : String → CInt → M World Unit) : M World Stream := do
  let stream ← construct (← allocate) statusUninit
  beginIO
  let loop ← eventloop
  let status ← initializeNative loop (← access.get stream).handle (cint 0)
  uvError "failed to create pipe endpoint" status
  access.set stream { (← access.get stream) with status := statusInit }
  endIO
  pure stream

-- UNTRANSLATED
-- Source: base/stream.jl:203-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:204-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function PipeEndpoint(fd::OS_HANDLE)
    pipe = PipeEndpoint()
    return open_pipe!(pipe, fd)
end
```
-/
def pipeEndpointFD {World Stream FD : Type}
    (construct : M World Stream) (openPipe : Stream → FD → M World Stream)
    (descriptor : FD) : M World Stream := do openPipe (← construct) descriptor

-- UNTRANSLATED
-- Source: base/stream.jl:208-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- if OS_HANDLE != RawFD
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    PipeEndpoint(fd::RawFD) = PipeEndpoint(Libc._get_osfhandle(fd))
```
-/
def pipeEndpointRawFD {World Stream RawFD OSHandle : Type}
    (getOSHandle : RawFD → M World OSHandle) (construct : OSHandle → M World Stream)
    (descriptor : RawFD) : M World Stream := do construct (← getOSHandle descriptor)

-- UNTRANSLATED
-- Source: base/stream.jl:210-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- 
-- mutable struct TTY <: LibuvStream
--     handle::Ptr{Cvoid}
--     status::Int
--     buffer::IOBuffer
--     cond::ThreadSynchronizer
--     readerror::Any
--     sendbuf::Union{IOBuffer, Nothing}
--     lock::ReentrantLock # advisory lock
--     throttle::Int
--     raw_lock::ReentrantLock # exclusive access to raw mode
--     @static if Sys.iswindows(); ispty::Bool; end
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:224-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function TTY(handle::Ptr{Cvoid}, status)
        tty = new(
            handle,
            status,
            PipeBuffer(),
            ThreadSynchronizer(),
            nothing,
            nothing,
            ReentrantLock(),
            DEFAULT_READ_BUFFER_SZ,
            ReentrantLock())
        associate_julia_struct(handle, tty)
        finalizer(uvfinalize, tty)
        @static if Sys.iswindows()
            tty.ispty = ccall(:jl_ispty, Cint, (Ptr{Cvoid},), handle) != 0
        end
        return tty
    end
```
-/
def ttyFromHandle {World Stream Buffer Condition Lock Status : Type}
    (toStatus : Status → M World I) (pipeBuffer : M World Buffer)
    (newCondition : M World Condition) (newLock : M World Lock)
    (newTTY : UVFields Buffer Condition Lock → Lock → M World Stream)
    (associate : Handle → Stream → M World Unit) (finalize : Stream → M World Unit)
    (isPty : Handle → M World CInt) (setPty : Stream → Bool → M World Unit)
    (windows : Bool) (handle : Handle) (status : Status) : M World Stream := do
  let status ← toStatus status
  let buffer ← pipeBuffer
  let condition ← newCondition
  let mutex ← newLock
  let rawMutex ← newLock
  let stream ← newTTY ⟨handle, status, buffer, condition, none, none, mutex, defaultReadBufferSize⟩ rawMutex
  associate handle stream
  finalize stream
  if windows then setPty stream ((← isPty handle).val != 0)
  pure stream

-- UNTRANSLATED
-- Source: base/stream.jl:242-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:244-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function TTY(fd::OS_HANDLE)
    tty = TTY(Libc.malloc(_sizeof_uv_tty), StatusUninit)
    iolock_begin()
    err = ccall(:uv_tty_init, Int32, (Ptr{Cvoid}, Ptr{Cvoid}, OS_HANDLE, Int32),
        eventloop(), tty.handle, fd, 0)
    uv_error("TTY", err)
    tty.status = StatusOpen
    iolock_end()
    return tty
end
```
-/
def ttyFD {World Stream Buffer Condition Lock FD : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (allocate : M World Handle) (construct : Handle → I → M World Stream)
    (beginIO endIO : M World Unit) (eventloop : M World Handle)
    (initializeNative : Handle → Handle → FD → CInt → M World CInt)
    (uvError : String → CInt → M World Unit) (descriptor : FD) : M World Stream := do
  let stream ← construct (← allocate) statusUninit
  beginIO
  let loop ← eventloop
  let status ← initializeNative loop (← access.get stream).handle descriptor (cint 0)
  uvError "TTY" status
  access.set stream { (← access.get stream) with status := statusOpen }
  endIO
  pure stream

-- UNTRANSLATED
-- Source: base/stream.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- if OS_HANDLE != RawFD
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    TTY(fd::RawFD) = TTY(Libc._get_osfhandle(fd))
```
-/
def ttyRawFD {World Stream RawFD OSHandle : Type}
    (getOSHandle : RawFD → M World OSHandle) (construct : OSHandle → M World Stream)
    (descriptor : RawFD) : M World Stream := do construct (← getOSHandle descriptor)

-- UNTRANSLATED
-- Source: base/stream.jl:256-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:258-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, stream::LibuvServer) = print(io, typeof(stream), "(",
    _fd(stream), " ",
    uv_status_string(stream), ")")
```
-/
def showServer {World Out Server Kind FD : Type}
    (typeof : Server → M World Kind) (fd : Server → M World FD)
    (status : Server → M World String) (print : Out → List (ShowArg Kind FD) → M World Unit)
    (out : Out) (server : Server) : M World Unit := do
  let kind ← typeof server
  let fd ← fd server
  let status ← status server
  print out [.kind kind, .text "(", .descriptor fd, .text " ", .text status, .text ")"]

/--
Julia source: base/stream.jl:261-264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, stream::LibuvStream) = print(io, typeof(stream), "(",
    _fd(stream), " ",
    uv_status_string(stream), ", ",
    bytesavailable(stream.buffer), " bytes waiting)")
```
-/
def showStream {World Stream Buffer Condition Lock Out Kind FD : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (typeof : Stream → M World Kind) (fd : Stream → M World FD)
    (status : Stream → M World String) (available : Buffer → M World I)
    (print : Out → List (ShowArg Kind FD) → M World Unit) (out : Out) (stream : Stream) : M World Unit := do
  let kind ← typeof stream
  let fd ← fd stream
  let status ← status stream
  let count ← available (← access.get stream).buffer
  print out [.kind kind, .text "(", .descriptor fd, .text " ", .text status,
    .text ", ", .count count, .text " bytes waiting)"]

-- UNTRANSLATED
-- Source: base/stream.jl:265-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Shared LibuvStream object interface
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:268-273 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isreadable(io::LibuvStream)
    bytesavailable(io) > 0 && return true
    isopen(io) || return false
    io.status == StatusEOF && return false
    return ccall(:uv_is_readable, Cint, (Ptr{Cvoid},), io.handle) != 0
end
```
-/
def isreadable {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (available : Stream → M World I) (isopen : Stream → M World Bool)
    (readable : Handle → M World CInt) (stream : Stream) : M World Bool := do
  if (← available stream).val > 0 then return true
  if !(← isopen stream) then return false
  if (← access.get stream).status.val = 7 then return false
  pure ((← readable (← access.get stream).handle).val != 0)

-- UNTRANSLATED
-- Source: base/stream.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:275-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iswritable(io::LibuvStream)
    isopen(io) || return false
    io.status == StatusClosing && return false
    return ccall(:uv_is_writable, Cint, (Ptr{Cvoid},), io.handle) != 0
end
```
-/
def iswritable {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (isopen : Stream → M World Bool) (writable : Handle → M World CInt)
    (stream : Stream) : M World Bool := do
  if !(← isopen stream) then return false
  if (← access.get stream).status.val = 5 then return false
  pure ((← writable (← access.get stream).handle).val != 0)

-- UNTRANSLATED
-- Source: base/stream.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lock(s::LibuvStream) = lock(s.lock)
```
-/
def lock {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (lock : Lock → M World Unit) (stream : Stream) : M World Unit := do
  lock (← access.get stream).mutex

/--
Julia source: base/stream.jl:282-282 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unlock(s::LibuvStream) = unlock(s.lock)
```
-/
def unlock {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (unlock : Lock → M World Unit) (stream : Stream) : M World Unit := do
  unlock (← access.get stream).mutex

-- UNTRANSLATED
-- Source: base/stream.jl:283-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:284-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setup_stdio(stream::Union{LibuvStream, LibuvServer}, ::Bool) = (stream, false)
```
-/
def setupStdio {Stream : Type} (stream : Stream) (_childReadable : Bool) : Stream × Bool := (stream, false)

/--
Julia source: base/stream.jl:285-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rawhandle(stream::Union{LibuvStream, LibuvServer}) = stream.handle
```
-/
def rawhandle {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (reference : Ref) : M World Handle := metadata.handle reference

/--
Julia source: base/stream.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_convert(::Type{Ptr{Cvoid}}, s::Union{LibuvStream, LibuvServer}) = s.handle
```
-/
def unsafeConvert {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (reference : Ref) : M World Handle := metadata.handle reference

-- Source: base/stream.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/stream.jl:315-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     open(fd::OS_HANDLE)::IO
-- 
-- Take a raw file descriptor and wrap it in a Julia-aware IO type,
-- and take ownership of the fd handle.
-- Call `open(Libc.dup(fd))` to avoid the ownership capture
-- of the original handle.
-- 
-- !!! warning
--     Do not call this on a handle that's already owned by some
--     other part of the system.
-- """
-- /Source

-- Source: base/stream.jl:362-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if OS_HANDLE != RawFD
-- /Source

-- Source: base/stream.jl:375-376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source

/--
Julia source: base/stream.jl:288-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function init_stdio(handle::Ptr{Cvoid})
    iolock_begin()
    t = ccall(:jl_uv_handle_type, Int32, (Ptr{Cvoid},), handle)
    local io
    if t == UV_FILE
        fd = ccall(:jl_uv_file_handle, OS_HANDLE, (Ptr{Cvoid},), handle)
        # TODO: Replace ios.c file with libuv fs?
        # return File(fd)
        @static if Sys.iswindows()
            # TODO: Get ios.c to understand native handles
            fd = ccall(:_open_osfhandle, RawFD, (WindowsRawSocket, Int32), fd, 0)
        end
        # TODO: Get fdio to work natively with file descriptors instead of integers
        io = fdio(cconvert(Cint, fd))
    elseif t == UV_TTY
        io = TTY(handle, StatusOpen)
    elseif t == UV_TCP
        Sockets = require_stdlib(PkgId(UUID((0x6462fe0b_24de_5631, 0x8697_dd941f90decc)), "Sockets"))
        io = Sockets.TCPSocket(handle, StatusOpen)
    elseif t == UV_NAMED_PIPE
        io = PipeEndpoint(handle, StatusOpen)
    else
        throw(ArgumentError("invalid stdio type: $t"))
    end
    iolock_end()
    return io
end
```
-/
def initStdio {World IO OSHandle RawFD Module Condition : Type}
    (p : StdioOps World IO OSHandle RawFD Module Condition) (windows : Bool) (handle : Handle) : M World IO := do
  p.beginIO
  let kind ← p.handleType handle
  let io ← if kind.val == p.fileType.val then do
      let fd ← p.fileHandle handle
      let fd ← if windows then p.convertRawFD (← p.openOSHandle fd (cint 0)) else p.convertOSFD fd
      p.fdio fd
    else if kind.val == p.ttyType.val then p.ttyHandle handle statusOpen
    else if kind.val == p.tcpType.val then do
      let sockets ← p.requireStdlib (u 0x6462fe0b24de5631) (u 0x8697dd941f90decc) "Sockets"
      p.tcpHandle sockets handle statusOpen
    else if kind.val == p.pipeType.val then p.pipeHandle handle statusOpen
    else throw (.jl (.argumentError ("invalid stdio type: " ++ p.formatType kind)))
  p.endIO
  pure io

/--
Julia source: base/stream.jl:328-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function open(h::OS_HANDLE)
    iolock_begin()
    t = ccall(:uv_guess_handle, Cint, (OS_HANDLE,), h)
    local io
    if t == UV_FILE
        @static if Sys.iswindows()
            # TODO: Get ios.c to understand native handles
            h = ccall(:_open_osfhandle, RawFD, (WindowsRawSocket, Int32), h, 0)
        end
        # TODO: Get fdio to work natively with file descriptors instead of integers
        io = fdio(cconvert(Cint, h))
    elseif t == UV_TTY
        io = TTY(h)
    elseif t == UV_TCP
        Sockets = require_stdlib(PkgId(UUID((0x6462fe0b_24de_5631, 0x8697_dd941f90decc)), "Sockets"))
        io = Sockets.TCPSocket(h)
    elseif t == UV_NAMED_PIPE
        io = PipeEndpoint(h)
        @static if Sys.iswindows()
            if ccall(:jl_ispty, Cint, (Ptr{Cvoid},), io.handle) != 0
                # replace the Julia `PipeEndpoint` type with a `TTY` type,
                # if we detect that this is a cygwin pty object
                pipe_handle, pipe_status = io.handle, io.status
                io.status = StatusClosed
                io.handle = C_NULL
                io = TTY(pipe_handle, pipe_status)
            end
        end
    else
        throw(ArgumentError("invalid stdio type: $t"))
    end
    iolock_end()
    return io
end
```
-/
def openOSHandle {World IO OSHandle RawFD Module Condition : Type}
    (p : StdioOps World IO OSHandle RawFD Module Condition) (windows : Bool) (handle : OSHandle) : M World IO := do
  p.beginIO
  let kind ← p.guessHandle handle
  let io ← if kind.val == p.fileType.val then do
      let fd ← if windows then p.convertRawFD (← p.openOSHandle handle (cint 0)) else p.convertOSFD handle
      p.fdio fd
    else if kind.val == p.ttyType.val then p.ttyFD handle
    else if kind.val == p.tcpType.val then do
      let sockets ← p.requireStdlib (u 0x6462fe0b24de5631) (u 0x8697dd941f90decc) "Sockets"
      p.tcpFD sockets handle
    else if kind.val == p.pipeType.val then do
      let mut pipe ← p.pipeFD handle
      if windows then
        if (← p.isPty (← p.metadata.handle pipe)).val != 0 then
          let pointer ← p.metadata.handle pipe
          let status ← p.metadata.status pipe
          p.metadata.setStatus pipe statusClosed
          p.metadata.setHandle pipe nullHandle
          pipe ← p.ttyHandle pointer status
      pure pipe
    else throw (.jl (.argumentError ("invalid stdio type: " ++ p.formatType kind)))
  p.endIO
  pure io

/--
Julia source: base/stream.jl:364-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function open(fd::RawFD)
        h = Libc.dup(Libc._get_osfhandle(fd)) # make a dup to steal ownership away from msvcrt
        try
            io = open(h)
            ccall(:_close, Cint, (RawFD,), fd) # on success, destroy the old libc handle
            return io
        catch ex
            ccall(:CloseHandle, stdcall, Cint, (OS_HANDLE,), h) # on failure, destroy the new nt handle
            rethrow(ex)
        end
    end
```
-/
def openRawFD {World IO RawFD OSHandle : Type}
    (getOSHandle : RawFD → M World OSHandle) (dup : OSHandle → M World OSHandle)
    (openStream : OSHandle → M World IO) (closeFD : RawFD → M World CInt)
    (closeHandle : OSHandle → M World CInt) (fd : RawFD) : M World IO := do
  let handle ← dup (← getOSHandle fd)
  tryCatch (do
    let io ← openStream handle
    let _ ← closeFD fd
    pure io) (fun error => do
      let _ ← closeHandle handle
      throw error)


/--
Julia source: base/stream.jl:377-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isopen(x::Union{LibuvStream, LibuvServer})
    if x.status == StatusUninit || x.status == StatusInit || x.handle === C_NULL
        throw(ArgumentError("stream not initialized"))
    end
    return x.status != StatusClosed
end
```
-/
def isopen {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (reference : Ref) : M World Bool := do
  if (← metadata.status reference).val = 0 then throw (.jl (.argumentError "stream not initialized"))
  if (← metadata.status reference).val = 1 then throw (.jl (.argumentError "stream not initialized"))
  if (← metadata.handle reference).address.val = 0 then throw (.jl (.argumentError "stream not initialized"))
  pure ((← metadata.status reference).val != 6)

-- UNTRANSLATED
-- Source: base/stream.jl:383-383 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:384-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_open(x::Union{LibuvStream, LibuvServer})
    if !isopen(x) || x.status == StatusClosing
        throw(IOError("stream is closed or unusable", 0))
    end
end
```
-/
def checkOpen {World Ref : Type} (status : Ref → M World I)
    (isopen : Ref → M World Bool) (reference : Ref) : M World Unit := do
  if !(← isopen reference) then throw (.foreignError "IOError" "stream is closed or unusable")
  if (← status reference).val = 5 then throw (.foreignError "IOError" "stream is closed or unusable")

-- Source: base/stream.jl:389-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/stream.jl:443-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## Waits on libuv requests
-- #
-- # A libuv request (write, shutdown, UDP send, DNS lookup) is issued under the
-- # iolock with its data field C_NULL and completes by a callback (also run
-- # under the iolock) that wakes the parked issuer through the standard
-- # wake-claim protocol. The request's data field tracks who owns freeing it:
-- #   pointer to the wait entry - a waiter is parked on the request;
-- #   C_NULL                    - the completion callback has run; the waiter
-- #                               owns the request;
-- #   UV_REQ_DETACHED           - the waiter departed (interrupted/refused
-- #                               wait, or fire-and-forget): the callback owns
-- #                               freeing it, plus any buffer root recorded in
-- #                               `_detached_uvreq_roots`.
-- 
-- # Sentinel for a uv request's data field: see above.
-- const UV_REQ_DETACHED = Ptr{Cvoid}(UInt(0x1))
-- 
-- # Aux word on a uv write wait's *witness* slot (the slot whose owner is the
-- # stream; its aux is otherwise unused). Every reader and writer runs under
-- # the iolock, so the packing needs no atomics:
-- #
-- #   bit  0      - CANCEL_REQUESTED: set immediately before Julia itself
-- #                 issues `uv_cancel` on write request(s) it keeps awaiting,
-- #                 so the completion callback can tell a Julia-requested
-- #                 cancellation (UV_ECANCELED is then the expected outcome,
-- #                 delivered as a partial-count wake) from a close-induced
-- #                 one (a real write error - libuv also fails queued writes
-- #                 with UV_ECANCELED when the stream closes).
-- #   bits 8..23  - the negated status of the first real error a chunk of a
-- #                 split write completed with (0 = none): a real error must
-- #                 win the final wake even when later chunks fail with the
-- #                 close-induced UV_ECANCELED cascade.
-- #   bits 32..63 - the number of pending completion callbacks of a split
-- #                 write. 0 means the wait is on a single request (the
-- #                 common case); a split write counts down here and only
-- #                 the callback that reaches 0 claims and wakes the waiter.
-- #
-- # Cleared whenever the slot is released for reuse (_release_slot!/
-- # _clear_uv_witness!). The detach paths do not set the flag: there the
-- # requests are detached in the same iolock critical section, so no callback
-- # can observe a waiter - the flag only matters to waited requests.
-- const _UVREQ_AUX_CANCEL_REQUESTED = UInt64(0x1)
-- const _UVREQ_AUX_STATUS_SHIFT = 8
-- const _UVREQ_AUX_STATUS_MASK = UInt64(0xffff) << _UVREQ_AUX_STATUS_SHIFT
-- const _UVREQ_AUX_PENDING_SHIFT = 32
-- 
-- # The witness slot of a uv-request wait entry: the one whose owner is
-- # neither empty nor the cancellation source. Callbacks locate it without
-- # knowing the witness object.
-- /Source

/--
Julia source: base/stream.jl:390-442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_readnb(x::LibuvStream, nb::Int, tok::MaybeToken=default_cancel_token())
    # fast path before iolock acquire
    bytesavailable(x.buffer) >= nb && return
    open = isopen(x) && x.status != StatusEOF # must precede readerror check
    x.readerror === nothing || throw(x.readerror)
    open || return
    iolock_begin()
    # repeat fast path after iolock acquire, before other expensive work
    bytesavailable(x.buffer) >= nb && (iolock_end(); return)
    open = isopen(x) && x.status != StatusEOF
    x.readerror === nothing || throw(x.readerror)
    open || (iolock_end(); return)
    # now do the "real" work
    oldthrottle = x.throttle
    preserve_handle(x)
    lock(x.cond)
    locked = true
    try
        while bytesavailable(x.buffer) < nb
            x.readerror === nothing || throw(x.readerror)
            isopen(x) || break
            x.status == StatusEOF && break
            x.throttle = max(nb, x.throttle)
            start_reading(x) # ensure we are reading
            iolock_end()
            locked = false
            wait(x.cond, tok)
            locked = true
            unlock(x.cond)
            locked = false
            iolock_begin()
            lock(x.cond)
            locked = true
        end
    finally
        # the teardown reads the waiter queue and the throttle under the
        # cond lock: reacquire when a wait-throw released this frame's
        # level (a spin lock; stop_reading takes the iolock itself)
        locked || lock(x.cond)
        if isempty(x.cond)
            stop_reading(x) # stop reading iff there are currently no other read clients of the stream
        end
        if oldthrottle <= x.throttle <= nb
            # if we're interleaving readers, we might not get back to the "original" throttle
            # but we consider that an acceptable "risk", since we can't be quite sure what the intended value is now
            x.throttle = oldthrottle
        end
        unpreserve_handle(x)
        unlock(x.cond)
    end
    iolock_end()
    nothing
end
```
-/
def waitReadnb {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (isopen : Stream → M World Bool) (beginIO endIO : M World Unit)
    (preserve unpreserve : Stream → M World Unit) (empty : Condition → M World Bool)
    (startReading : Stream → M World CInt) (stopReading : Stream → M World Unit)
    (stream : Stream) (count : I) (token : Option Token) : M World Unit := do
  if (← buffers.available (← access.get stream).buffer).val ≥ count.val then return ()
  let readable ← if ← isopen stream then pure ((← access.get stream).status.val != 7) else pure false
  match (← access.get stream).readerror with
  | some error => throw error
  | none => pure ()
  if !readable then return ()
  beginIO
  if (← buffers.available (← access.get stream).buffer).val ≥ count.val then
    endIO
    return ()
  let readable ← if ← isopen stream then pure ((← access.get stream).status.val != 7) else pure false
  match (← access.get stream).readerror with
  | some error => throw error
  | none => pure ()
  if !readable then
    endIO
    return ()
  let oldThrottle := (← access.get stream).throttle
  preserve stream
  ops.lock (← access.get stream).condition
  JuliaLean.base.locks_mt.runFrame true (JuliaLean.base.io.finallyDo (do
    JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
      if (← JuliaLean.base.locks_mt.liftFrame (do buffers.available (← access.get stream).buffer)).val ≥ count.val then return .inl ()
      match (← JuliaLean.base.locks_mt.liftFrame (access.get stream)).readerror with
      | some error => throw error
      | none => pure ()
      if !(← JuliaLean.base.locks_mt.liftFrame (isopen stream)) then return .inl ()
      if (← JuliaLean.base.locks_mt.liftFrame (access.get stream)).status.val == 7 then return .inl ()
      let fields ← JuliaLean.base.locks_mt.liftFrame (access.get stream)
      JuliaLean.base.locks_mt.liftFrame (access.set stream { fields with throttle := if count.val ≥ fields.throttle.val then count else fields.throttle })
      let _ ← JuliaLean.base.locks_mt.liftFrame (startReading stream)
      JuliaLean.base.locks_mt.liftFrame endIO
      JuliaLean.base.locks_mt.setFrame false
      JuliaLean.base.locks_mt.liftFrame (do ops.wait (← access.get stream).condition token)
      JuliaLean.base.locks_mt.setFrame true
      JuliaLean.base.locks_mt.liftFrame (do ops.unlock (← access.get stream).condition)
      JuliaLean.base.locks_mt.setFrame false
      JuliaLean.base.locks_mt.liftFrame beginIO
      JuliaLean.base.locks_mt.liftFrame (do ops.lock (← access.get stream).condition)
      JuliaLean.base.locks_mt.setFrame true
      pure (.inr ())) ()) (do
        if !(← JuliaLean.base.locks_mt.getFrame) then JuliaLean.base.locks_mt.liftFrame (do ops.lock (← access.get stream).condition)
        if ← JuliaLean.base.locks_mt.liftFrame (do empty (← access.get stream).condition) then
          JuliaLean.base.locks_mt.liftFrame (stopReading stream)
        let current ← JuliaLean.base.locks_mt.liftFrame (access.get stream)
        if oldThrottle.val ≤ current.throttle.val && current.throttle.val ≤ count.val then
          JuliaLean.base.locks_mt.liftFrame (access.set stream { current with throttle := oldThrottle })
        JuliaLean.base.locks_mt.liftFrame (unpreserve stream)
        JuliaLean.base.locks_mt.liftFrame (do ops.unlock (← access.get stream).condition)))
  endIO


/--
Julia source: base/stream.jl:493-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uvreq_witness_slot(w::WaitEntry)
    for (i, slot) in enumerate(slots(w))
        o = slot.owner
        (o === nothing || o isa CancellationTokenSource) && continue
        return i
    end
    return 0
end
```
-/
def uvreqWitnessSlot {World Entry Slot Source Owner : Type}
    (slots : Entry → M World (List Slot))
    (owner : Slot → M World (Option (Sum Source Owner))) (entry : Entry) : M World I := do
  for (slot, index) in (← slots entry).zipIdx do
    match ← owner slot with
    | none | some (.inl _) => pure ()
    | some (.inr _) => return i (index + 1)
  pure (i 0)

-- UNTRANSLATED
-- Source: base/stream.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:502-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _mark_uvreq_cancel_requested!(w::WaitEntry, @nospecialize(witness))
    i = _find_slot(w, witness)
    i == 0 || _set_slot_aux!(w, i, _slot_aux(w, i) | _UVREQ_AUX_CANCEL_REQUESTED)
    return nothing
end
```
-/
def markUVRequestCancelled {World Entry Witness : Type}
    (findSlot : Entry → Witness → M World I) (getAux : Entry → I → M World U)
    (setAux : Entry → I → U → M World Unit) (entry : Entry) (witness : Witness) : M World Unit := do
  let slot ← findSlot entry witness
  if slot.val != 0 then
    setAux entry slot (JuliaLean.base.int.or_int (← getAux entry slot) (u 1))

-- UNTRANSLATED
-- Source: base/stream.jl:507-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Whether the waiter flagged this request's cancellation as its own. Read
-- # by the completion callback (under the iolock) *before* the claim releases
-- # the witness slot.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:511-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uvreq_cancel_requested(req::Ptr{Cvoid})
    d = uv_req_data(req)
    (d == C_NULL || d == UV_REQ_DETACHED) && return false
    w = unsafe_pointer_to_objref(d)::WaitEntry
    i = _uvreq_witness_slot(w)
    return i != 0 && _slot_aux(w, i) & _UVREQ_AUX_CANCEL_REQUESTED != 0
end
```
-/
def uvreqCancelRequested {World Entry : Type}
    (requestData : Handle → M World Handle) (toEntry : Handle → M World Entry)
    (witnessSlot : Entry → M World I) (getAux : Entry → I → M World U)
    (request : Handle) : M World Bool := do
  let data ← requestData request
  if data.address.val = 0 || data.address.val = 1 then return false
  let entry ← toEntry data
  let slot ← witnessSlot entry
  if slot.val = 0 then return false
  pure ((JuliaLean.base.int.and_int (← getAux entry slot) (u 1)).val != 0)

-- UNTRANSLATED
-- Source: base/stream.jl:518-529 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Buffers of detached write requests. A detached request keeps referencing
-- # the caller's memory until its completion callback runs - long after the
-- # issuing frame, whose GC.@preserve was the buffer's only root, has unwound.
-- # When the write's Julia owner is known it is rooted here, keyed by the
-- # request, and released by the completion callback. Guarded by the iolock
-- # (callbacks run under it). Raw-pointer writes (the generic unsafe_write
-- # interface) have no discoverable owner - their contract is pointer validity
-- # for the duration of the call - and detaching them retains the pre-existing
-- # hazard; owner-carrying entry points avoid it.
-- const _detached_uvreq_roots = IdDict{Ptr{Cvoid}, Any}()
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:530-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _root_detached_uvreq!(req::Ptr{Cvoid}, @nospecialize(owner))
    owner === nothing || (_detached_uvreq_roots[req] = owner)
    return nothing
end
```
-/
def rootDetachedRequest {World Owner : Type}
    (set : Handle → Owner → M World Unit) (request : Handle) (owner : Option Owner) : M World Unit := do
  match owner with
  | none => pure ()
  | some owner => set request owner

/--
Julia source: base/stream.jl:534-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_unroot_detached_uvreq!(req::Ptr{Cvoid}) =
    (isempty(_detached_uvreq_roots) || delete!(_detached_uvreq_roots, req); nothing)
```
-/
def unrootDetachedRequest {World Result : Type}
    (empty : M World Bool) (delete : Handle → M World Result) (request : Handle) : M World Unit := do
  if !(← empty) then let _ ← delete request
  pure ()

-- UNTRANSLATED
-- Source: base/stream.jl:536-539 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # The entry check of a cancellable uv operation, made under the iolock
-- # before the request is issued: when `src` is already cancelled, release the
-- # iolock and throw the request - before the operation has any side effects.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:540-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _iolocked_checkcancel(src::Union{Nothing, CancellationTokenSource})
    if src !== nothing && iscancelled(src)
        iolock_end()
        checkcancel(src)
    end
    return nothing
end
```
-/
def iolockedCheckcancel {World Source : Type}
    (cancelled : Source → M World Bool) (endIO : M World Unit)
    (checkcancel : Source → M World Unit) (source : Option Source) : M World Unit := do
  match source with
  | none => pure ()
  | some source =>
    if ← cancelled source then
      endIO
      checkcancel source

-- Source: base/stream.jl:547-552 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Arm the wait for the issued uv request `req`: pick the wait entry (with a
-- # cancellation-source slot when governed by `src`), arm it, record `witness`
-- # (the waitee identity - the handle, or the request itself when there is
-- # none) as the entry's reuse gate, and point the request at the entry.
-- # Leaves the caller's iolock held, inside a sigatomic section.
-- /Source

-- Source: base/stream.jl:564-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Wind down a uv request wait (caller holds the iolock, at the sigatomic
-- # level of the wait): resolve the request's ownership, release the wait
-- # witness, disarm the registration (a no-op when a claimer already did),
-- # and unwind the iolock, the sigatomic section, and the handle preservation.
-- # When the completion callback has already run (data == C_NULL) the request
-- # is ours to free; otherwise - the wait was interrupted or refused, or the
-- # task was resumed by an unexpected `schedule` - the request is detached for
-- # the callback to free, `uv_cancel`ed first when `trycancel` is set (so e.g.
-- # an abandoned write stops spamming the stream), with `owner` kept rooted
-- # until then. The sticky source registration needs no cleanup at all.
-- /Source

-- Source: base/stream.jl:598-614 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## An in-flight libuv request as a waitable (see base/park.jl): the
-- ## held-resource kind. The caller issues the request under the iolock and
-- ## keeps it held into `park!` - the completion callback runs under that
-- ## same lock, so the recheck is vacuous - and the request's data pointer
-- ## doubles as the completion/detach handshake: the dequeue resolves its
-- ## ownership on every exit path (callback already ran => we free it;
-- ## otherwise it is detached to the callback, `uv_cancel`ed when
-- ## requested, with the write's buffer kept rooted until then). The
-- ## dequeue also consumes the reacquired iolock/sigatomic bracket.
-- struct UvReqWait
--     req::Ptr{Cvoid}
--     witness::Any      # the waitee identity (the handle, or the request)
--     owner::Any        # buffer root for a detached request
--     trycancel::Bool
-- end
-- 
-- /Source

-- Source: base/stream.jl:620-625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Resolve the request's ownership and release the witness. On
-- # WAKE_VALUE/WAKE_FIRED the caller holds the iolock (the settle and the
-- # refusal both run under it); the cleanup why takes it itself. The
-- # iolock/sigatomic/handle-preservation choreography around the park is
-- # the site's own code (_wait_uvreq, _uv_write_wait).
-- /Source

-- Source: base/stream.jl:641-649 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Park on the completion of the issued uv request `req` and return the value
-- # its completion callback delivers. A cancellation of `src` interrupts the
-- # wait and throws the CancellationRequest - without parking at all when
-- # `src` got cancelled between the caller's entry check and the registration
-- # here; either way the request is left to its callback (see the dequeue
-- # above). The caller must have issued `req` under the still-held iolock -
-- # so the callback cannot have run yet - and gets it back with the iolock
-- # released.
-- /Source

-- Source: base/stream.jl:692-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Completion-callback side of the wait (runs under the iolock): resolve
-- # request ownership and claim the parked waiter's wake. Returns the task to
-- # schedule, or `nothing` when there is nobody to wake - either no waiter
-- # remains (fire-and-forget, or the waiter departed and detached the request,
-- # which is freed here together with any recorded buffer root), or a
-- # canceller claimed the wake first (the waiter's teardown then observes
-- # data == C_NULL and takes over the request).
-- /Source

-- Source: base/stream.jl:718-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/stream.jl:749-749 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/stream.jl:553-563 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _begin_uvreq_wait!(src::Union{Nothing, CancellationTokenSource},
                            @nospecialize(witness), req::Ptr{Cvoid})
    ct = current_task()
    w = src === nothing ? _cached_wait_entry(ct) : _cancel_wait_entry(ct, src, 0x00)
    _arm_wait(ct, w)
    _set_wait_witness!(w, witness)
    preserve_handle(ct)
    sigatomic_begin()
    uv_req_set_data(req, pointer_from_objref(w))
    return w
end
```
-/
def beginUVRequestWait {World Task Entry Source Witness Owner Queue Result : Type}
    (p : RequestOps World Task Entry Source Witness Owner Queue Result)
    (source : Option Source) (witness : Witness) (request : Handle) : M World Entry := do
  let task ← p.currentTask
  let entry ← match source with
    | none => p.cachedEntry task
    | some source => p.cancelEntry task source (JuliaLean.base.io.byte 0)
  p.arm task entry
  p.setWitness entry witness
  p.preserve task
  p.sigatomicBegin
  p.setData request (← p.entryPointer entry)
  pure entry

/--
Julia source: base/stream.jl:575-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _end_uvreq_wait!(w::WaitEntry, @nospecialize(witness), req::Ptr{Cvoid},
                          trycancel::Bool, @nospecialize(owner))
    ct = current_task()
    if uv_req_data(req) == C_NULL
        Libc.free(req)
    else
        trycancel && ccall(:uv_cancel, Cint, (Ptr{Cvoid},), req) # ignore any errors
        uv_req_set_data(req, UV_REQ_DETACHED)
        _root_detached_uvreq!(req, owner)
    end
    _clear_wait_witness!(w, witness)
    @atomicreplace ct.waiting_on w => nothing
    # Drop a claimed-and-enqueued wake an interrupted teardown will never
    # consume. The completion callback claims and schedules under the
    # iolock this function holds, so the drop is deterministic here (cf.
    # the interrupted cleanup in base/park.jl).
    q = ct.queue
    q === nothing || list_deletefirst!(q::StickyWorkqueue, ct)
    iolock_end()
    sigatomic_end()
    unpreserve_handle(ct)
    return nothing
end
```
-/
def endUVRequestWait {World Task Entry Source Witness Owner Queue Result : Type}
    (p : RequestOps World Task Entry Source Witness Owner Queue Result)
    (entry : Entry) (witness : Witness) (request : Handle) (trycancel : Bool) (owner : Option Owner) : M World Unit := do
  let task ← p.currentTask
  if (← p.data request).address.val == 0 then p.free request
  else
    if trycancel then let _ ← p.cancel request
    p.setData request ⟨u 1⟩
    p.rootDetached request owner
  p.clearWitness entry witness
  let _ ← p.replaceWaiting .sequentiallyConsistent .sequentiallyConsistent task (some entry) none
  match ← p.queue task with
  | none => pure ()
  | some queue => p.deleteFirst queue task
  p.endIO
  p.sigatomicEnd
  p.unpreserve task

/--
Julia source: base/stream.jl:615-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_enqueue!(x::UvReqWait, w::WaitEntry, first::Bool)
    _set_wait_witness!(w, x.witness)
    uv_req_set_data(x.req, pointer_from_objref(w))
    return true
end
```
-/
def uvRequestEnqueue {World Task Entry Source Witness Owner Queue Result : Type}
    (p : RequestOps World Task Entry Source Witness Owner Queue Result)
    (request : UvReqWait Witness Owner) (entry : Entry) (_first : Bool) : M World Bool := do
  p.setWitness entry request.witness
  p.setData request.request (← p.entryPointer entry)
  pure true

/--
Julia source: base/stream.jl:626-640 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_dequeue!(x::UvReqWait, w::WaitEntry, why::UInt8)
    selflock = why == WAKE_INTERRUPTED || why == WAKE_WITHDRAWN
    selflock && iolock_begin()
    req = x.req
    if uv_req_data(req) == C_NULL
        Libc.free(req)
    else
        x.trycancel && ccall(:uv_cancel, Cint, (Ptr{Cvoid},), req) # ignore any errors
        uv_req_set_data(req, UV_REQ_DETACHED)
        _root_detached_uvreq!(req, x.owner)
    end
    _clear_wait_witness!(w, x.witness)
    selflock && iolock_end()
    return nothing
end
```
-/
def uvRequestDequeue {World Task Entry Source Witness Owner Queue Result : Type}
    (p : RequestOps World Task Entry Source Witness Owner Queue Result)
    (request : UvReqWait Witness Owner) (entry : Entry) (why : Byte) : M World Unit := do
  let selflock := why.val == p.wakeInterrupted.val || why.val == p.wakeWithdrawn.val
  if selflock then p.beginIO
  if (← p.data request.request).address.val == 0 then p.free request.request
  else
    if request.trycancel then let _ ← p.cancel request.request
    p.setData request.request ⟨u 1⟩
    p.rootDetached request.request request.owner
  p.clearWitness entry request.witness
  if selflock then p.endIO

/--
Julia source: base/stream.jl:650-691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _wait_uvreq(src::Union{Nothing, CancellationTokenSource}, @nospecialize(witness),
                     req::Ptr{Cvoid}, trycancel::Bool, @nospecialize(owner))
    ct = current_task()
    uvw = UvReqWait(req, witness, owner, trycancel)
    if src === nothing
        ws = (uvw,)
        w = _cached_wait_entry(ct)
    else
        ws = (uvw, SourceWait(src, 0x00))
        w = _cancel_wait_entry(ct, src, 0x00)
    end
    preserve_handle(ct)
    sigatomic_begin()
    if !park!(ws, w, false)
        # refused at the registration recheck: resolve the request under
        # the still-held iolock, unwind the brackets, deliver
        withdraw!(ws, w, WAKE_FIRED)
        iolock_end()
        sigatomic_end()
        unpreserve_handle(ct)
        checkcancel(src)
        error("park fired without a cancelled source")
    end
    iolock_end()
    sigatomic_end()
    local r
    try
        r = wait_safe_interrupt(ws, w)
    catch
        # (the catch restored the sigatomic level from the try entry; the
        # cleanup's dequeue resolved the request under its own iolock)
        unpreserve_handle(ct)
        rethrow()
    end
    sigatomic_begin()
    iolock_begin()
    withdraw!(ws, w, WAKE_VALUE)   # resolve the request under the iolock
    iolock_end()
    sigatomic_end()
    unpreserve_handle(ct)
    return r
end
```
-/
def waitUVRequest {World Task Entry Source Witness Owner Queue Result : Type}
    (p : RequestOps World Task Entry Source Witness Owner Queue Result)
    (source : Option Source) (witness : Witness) (request : Handle) (trycancel : Bool) (owner : Option Owner) : M World Result := do
  let task ← p.currentTask
  let requestWait : UvReqWait Witness Owner := ⟨request, witness, owner, trycancel⟩
  let (waitables, entry) ← match source with
    | none => do
      let entry ← p.cachedEntry task
      pure ([RequestWaitable.request requestWait], entry)
    | some source => do
      let entry ← p.cancelEntry task source (JuliaLean.base.io.byte 0)
      pure ([RequestWaitable.request requestWait, RequestWaitable.source source (JuliaLean.base.io.byte 0)], entry)
  p.preserve task
  p.sigatomicBegin
  if !(← p.park waitables entry false) then
    p.withdraw waitables entry p.wakeFired
    p.endIO
    p.sigatomicEnd
    p.unpreserve task
    p.checkCancel source
    throw (.errorException "park fired without a cancelled source")
  p.endIO
  p.sigatomicEnd
  let result ← tryCatch (p.waitSafe waitables entry) (fun error => do
    p.unpreserve task
    throw error)
  p.sigatomicBegin
  p.beginIO
  p.withdraw waitables entry p.wakeValue
  p.endIO
  p.sigatomicEnd
  p.unpreserve task
  pure result

/--
Julia source: base/stream.jl:700-717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _claim_uvreq_waiter(req::Ptr{Cvoid})
    d = uv_req_data(req)
    if d == C_NULL || d == UV_REQ_DETACHED
        _unroot_detached_uvreq!(req)
        Libc.free(req)
        return nothing
    end
    # mark the callback as done; the waiter (which inspects the request
    # under the iolock) owns freeing it
    uv_req_set_data(req, C_NULL)
    w = unsafe_pointer_to_objref(d)::WaitEntry
    t = @atomic :monotonic w.task
    if t isa Task && claim_wait(t, w)
        _clear_uv_witness!(w)
        return t
    end
    return nothing
end
```
-/
def claimUVRequestWaiter {World Task Entry Source Witness Owner Queue Result : Type}
    (p : RequestOps World Task Entry Source Witness Owner Queue Result) (request : Handle) : M World (Option Task) := do
  let data ← p.data request
  if data.address.val == 0 || data.address.val == 1 then
    p.unrootDetached request
    p.free request
    return none
  p.setData request nullHandle
  let entry ← p.pointerEntry data
  match ← p.entryTask .monotonic entry with
  | none => pure none
  | some task =>
    if ← p.claim task entry then
      p.clearUVWitness entry
      return some task
    pure none

/--
Julia source: base/stream.jl:719-748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function closewrite(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    iolock_begin()
    if !iswritable(s)
        iolock_end()
        return
    end
    src = cancel_source(resolve_cancel_token(cancel))
    # entry check: throw before issuing the shutdown request
    _iolocked_checkcancel(src)
    req = Libc.malloc(_sizeof_uv_shutdown)
    uv_req_set_data(req, C_NULL) # in case we get interrupted before arriving at the wait call
    err = ccall(:uv_shutdown, Int32, (Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}),
                req, s, @cfunction(uv_shutdowncb_task, Cvoid, (Ptr{Cvoid}, Cint)))
    if err < 0
        Libc.free(req)
        uv_error("shutdown", err)
    end
    # A shutdown request itself cannot be cancelled, so an interrupted wait
    # detaches it (its completion callback frees it).
    status = _wait_uvreq(src, s, req, false, nothing)::Cint
    if isopen(s)
        if status < 0 || ccall(:uv_is_readable, Cint, (Ptr{Cvoid},), s.handle) == 0
            close(s)
        end
    end
    if status < 0
        throw(_UVError("shutdown", status))
    end
    nothing
end
```
-/
def closewrite {World Stream Buffer Condition Lock Task Entry Source Owner Queue Result Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (p : RequestOps World Task Entry Source Stream Owner Queue Result)
    (iswritable isopen : Stream → M World Bool) (resolve : CancelArg Token → M World (Option Token))
    (sourceOf : Option Token → Option Source) (checkcancel : Option Source → M World Unit)
    (allocate : M World Handle) (shutdown : Handle → Stream → Handle → M World CInt)
    (callback : Handle) (uvError : String → CInt → M World Unit) (assertCint : Result → M World CInt)
    (readable : Handle → M World CInt) (close : Stream → M World Unit)
    (makeUVError : String → CInt → Error) (stream : Stream) (cancel : CancelArg Token) : M World Unit := do
  p.beginIO
  if !(← iswritable stream) then
    p.endIO
    return ()
  let source := sourceOf (← resolve cancel)
  checkcancel source
  let request ← allocate
  p.setData request nullHandle
  let error ← shutdown request stream callback
  if error.val < 0 then
    p.free request
    uvError "shutdown" error
  let status ← assertCint (← waitUVRequest p source stream request false none)
  if ← isopen stream then
    let failed ← if status.val < 0 then pure true else pure ((← readable (← access.get stream).handle).val == 0)
    if failed then close stream
  if status.val < 0 then throw (makeUVError "shutdown" status)


/--
Julia source: base/stream.jl:750-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_close(x::Union{LibuvStream, LibuvServer})
    preserve_handle(x)
    lock(x.cond)
    locked = true
    try
        while isopen(x)
            # close is the cleanup primitive: its completion wait is shielded
            # from cancellation (completion depends only on the event loop,
            # not on any peer, so this wait is bounded)
            locked = false
            wait(x.cond, nothing)
            locked = true
        end
    finally
        locked && unlock(x.cond)
        unpreserve_handle(x)
    end
    nothing
end
```
-/
def waitClose {World Ref Condition Token : Type} (metadata : Metadata World Ref Condition)
    (ops : ConditionOps World Condition Token) (preserve unpreserve : Ref → M World Unit)
    (isopen : Ref → M World Bool) (reference : Ref) : M World Unit := do
  preserve reference
  ops.lock (← metadata.condition reference)
  let (locked, result) ← conditionWaitLoop (isopen reference)
    (do ops.wait (← metadata.condition reference) none)
  JuliaLean.base.io.finallyDo (rethrowResult result) (do
    if locked then ops.unlock (← metadata.condition reference)
    unpreserve reference)

-- UNTRANSLATED
-- Source: base/stream.jl:769-769 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:770-784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function close(stream::Union{LibuvStream, LibuvServer})
    iolock_begin()
    if stream.status == StatusInit
        ccall(:jl_forceclose_uv, Cvoid, (Ptr{Cvoid},), stream.handle)
        stream.status = StatusClosing
    elseif isopen(stream)
        if stream.status != StatusClosing
            ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), stream.handle)
            stream.status = StatusClosing
        end
    end
    iolock_end()
    wait_close(stream)
    nothing
end
```
-/
def close {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (beginIO endIO : M World Unit) (forceClose closeHandle : Handle → M World Unit)
    (isopen : Ref → M World Bool) (waitClose : Ref → M World Unit)
    (reference : Ref) : M World Unit := do
  beginIO
  if (← metadata.status reference).val = 1 then
    forceClose (← metadata.handle reference)
    metadata.setStatus reference statusClosing
  else if ← isopen reference then
    if (← metadata.status reference).val != 5 then
      closeHandle (← metadata.handle reference)
      metadata.setStatus reference statusClosing
  endIO
  waitClose reference

-- UNTRANSLATED
-- Source: base/stream.jl:785-785 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:786-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uvfinalize(uv::Union{LibuvStream, LibuvServer})
    iolock_begin()
    if uv.handle != C_NULL
        disassociate_julia_struct(uv.handle) # not going to call the usual close hooks (so preserve_handle is not needed)
        if uv.status == StatusUninit
            Libc.free(uv.handle)
        elseif uv.status == StatusInit
            ccall(:jl_forceclose_uv, Cvoid, (Ptr{Cvoid},), uv.handle)
        elseif isopen(uv)
            if uv.status != StatusClosing
                ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), uv.handle)
            end
        elseif uv.status == StatusClosed
            Libc.free(uv.handle)
        end
        uv.handle = C_NULL
        uv.status = StatusClosed
    end
    iolock_end()
    nothing
end
```
-/
def uvfinalize {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (beginIO endIO : M World Unit) (disassociate free forceClose closeHandle : Handle → M World Unit)
    (isopen : Ref → M World Bool) (reference : Ref) : M World Unit := do
  beginIO
  if (← metadata.handle reference).address.val != 0 then
    disassociate (← metadata.handle reference)
    if (← metadata.status reference).val = 0 then free (← metadata.handle reference)
    else if (← metadata.status reference).val = 1 then forceClose (← metadata.handle reference)
    else if ← isopen reference then
      if (← metadata.status reference).val != 5 then closeHandle (← metadata.handle reference)
    else if (← metadata.status reference).val = 6 then free (← metadata.handle reference)
    metadata.setHandle reference nullHandle
    metadata.setStatus reference statusClosed
  endIO

-- UNTRANSLATED
-- Source: base/stream.jl:807-808 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if Sys.iswindows()
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:809-809 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ispty(s::TTY) = s.ispty
```
-/
def isptyTTY {World TTY : Type} (getPty : TTY → M World Bool) (stream : TTY) : M World Bool := getPty stream

/--
Julia source: base/stream.jl:810-810 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ispty(s::IO) = false
```
-/
def isptyIO {Stream : Type} (_stream : Stream) : Bool := false

-- UNTRANSLATED
-- Source: base/stream.jl:811-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- """
--     displaysize([io::IO]) -> (lines, columns)
-- 
-- Return the nominal size of the screen that may be used for rendering output to
-- this `IO` object.
-- If no input is provided, the environment variables `LINES` and `COLUMNS` are read.
-- If those are not set, a default size of `(24, 80)` is returned.
-- 
-- # Examples
-- ```jldoctest
-- julia> withenv("LINES" => 30, "COLUMNS" => 100) do
--            displaysize()
--        end
-- (30, 100)
-- ```
-- 
-- To get your TTY size,
-- 
-- ```julia-repl
-- julia> displaysize(stdout)
-- (34, 147)
-- ```
-- """
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:836-836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
displaysize(io::IO) = displaysize()
```
-/
def displaysizeIO {World Stream : Type} (displaysize : M World (I × I)) (_stream : Stream) : M World (I × I) :=
  displaysize

/--
Julia source: base/stream.jl:837-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
displaysize() = (parse(Int, get(ENV, "LINES",   "24")),
                 parse(Int, get(ENV, "COLUMNS", "80")))::Tuple{Int, Int}
```
-/
def displaysize {World : Type} (getEnv : String → String → M World String)
    (parse : String → M World I) : M World (I × I) := do
  let height ← parse (← getEnv "LINES" "24")
  let width ← parse (← getEnv "COLUMNS" "80")
  pure (height, width)

-- UNTRANSLATED
-- Source: base/stream.jl:839-844 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # This is a fancy way to de-specialize a call to `displaysize(io::IO)`
-- # which is unfortunately invalidated by REPL
-- #  (https://github.com/JuliaLang/julia/issues/56080)
-- #
-- # This makes the call less efficient, but avoids being invalidated by REPL.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:845-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
displaysize_(io::IO) = Base.invoke_in_world(Base.tls_world_age(), displaysize, io)::Tuple{Int,Int}
```
-/
def displaysizeWorld {World Stream Age : Type}
    (worldAge : M World Age) (invoke : Age → Stream → M World (I × I))
    (stream : Stream) : M World (I × I) := do invoke (← worldAge) stream

-- Source: base/stream.jl:846-846 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/stream.jl:880-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ### Libuv callbacks ###
-- 
-- ## BUFFER ##
-- ## Allocate space in buffer (for immediate use)
-- /Source

/--
Julia source: base/stream.jl:847-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function displaysize(io::TTY)
    check_open(io)

    local h::Int, w::Int
    default_size = displaysize()

    @static if Sys.iswindows()
        if ispty(io)
            # io is actually a libuv pipe but a cygwin/msys2 pty
            try
                h, w = parse.(Int, split(read(open(Base.Cmd(String["stty", "size"]), "r", io).out, String)))
                h > 0 || (h = default_size[1])
                w > 0 || (w = default_size[2])
                return h, w
            catch
                return default_size
            end
        end
    end

    s1 = Ref{Int32}(0)
    s2 = Ref{Int32}(0)
    iolock_begin()
    check_open(io)
    # A failed query (e.g. the fd stopped being a terminal) leaves s1/s2 at 0
    # and falls through to the default size below.
    ccall(:uv_tty_get_winsize, Int32, (Ptr{Cvoid}, Ptr{Int32}, Ptr{Int32}), io, s1, s2)
    iolock_end()
    w, h = s1[], s2[]
    h > 0 || (h = default_size[1])
    w > 0 || (w = default_size[2])
    return h, w
end
```
-/
def displaysizeTTY {World IO Command Process Input Pieces Parsed Ref : Type}
    (p : TTYSizeOps World IO Command Process Input Pieces Parsed Ref) (windows : Bool) (io : IO) : M World (I × I) := do
  p.checkOpen io
  let fallback ← p.defaultSize
  if windows then
    if ← p.isPty io then
      return ← tryCatch (do
        let command ← p.command ["stty", "size"]
        let process ← p.openProcess command "r" io
        let parsed ← p.parseInts (← p.split (← p.readString (← p.processOutput process)))
        let (height, width) ← p.firstTwo parsed
        pure (if height.val > 0 then height else fallback.1, if width.val > 0 then width else fallback.2))
        (fun _ => pure fallback)
  let first ← p.newRef (cint 0)
  let second ← p.newRef (cint 0)
  p.beginIO
  p.checkOpen io
  let _ ← p.getWinSize io first second
  p.endIO
  let width ← p.readRef first
  let height ← p.readRef second
  pure (if height.val > 0 then i height.val else fallback.1, if width.val > 0 then i width.val else fallback.2)


/--
Julia source: base/stream.jl:885-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function alloc_request(buffer::IOBuffer, recommended_size::UInt)
    ensureroom(buffer, recommended_size)
    ptr = buffer.append ? buffer.size + 1 : buffer.ptr
    start_offset = ptr - 1
    nb = max(0, min(length(buffer.data) - start_offset, buffer.maxsize - (start_offset - get_offset(buffer))))
    return (Ptr{Cvoid}(pointer(buffer.data, ptr)), nb)
end
```
-/
def allocRequest {World Buffer Data : Type}
    (access : JuliaLean.base.iobuffer.Access (M World) Buffer Data)
    (ensure : Buffer → U → M World Unit) (length : Data → M World I)
    (pointer : Data → I → M World BytePointer) (buffer : Buffer) (recommended : U) : M World (Handle × I) := do
  ensure buffer recommended
  let fields ← access.get buffer
  let position := if fields.append then fields.size + i 1 else fields.ptr
  let startOffset := position - i 1
  let length ← length (← access.get buffer).data
  let maximum := (← access.get buffer).maxsize
  let offset := JuliaLean.base.iobuffer.fieldsOffset (← access.get buffer)
  let available := length - startOffset
  let capacity := maximum - (startOffset - offset)
  let count := if available.val < capacity.val then available else capacity
  let count := if count.val < 0 then i 0 else count
  let data ← pointer (← access.get buffer).data position
  pure (⟨data.address⟩, count)

-- UNTRANSLATED
-- Source: base/stream.jl:892-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:893-893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
notify_filled(buffer::IOBuffer, nread::Int, base::Ptr{Cvoid}, len::UInt) = notify_filled(buffer, nread)
```
-/
def notifyFilledPointer {World Buffer : Type} (notify : Buffer → I → M World Unit)
    (buffer : Buffer) (count : I) (_base : Handle) (_length : U) : M World Unit := notify buffer count

-- UNTRANSLATED
-- Source: base/stream.jl:894-894 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:895-903 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function notify_filled(buffer::IOBuffer, nread::Int)
    if buffer.append
        buffer.size += nread
    else
        buffer.ptr += nread
        buffer.size = max(buffer.size, buffer.ptr - 1)
    end
    nothing
end
```
-/
def notifyFilled {World Buffer Data : Type}
    (access : JuliaLean.base.iobuffer.Access (M World) Buffer Data)
    (buffer : Buffer) (count : I) : M World Unit := do
  let fields ← access.get buffer
  if fields.append then access.set buffer { fields with size := fields.size + count }
  else
    access.set buffer { fields with ptr := fields.ptr + count }
    let fields ← access.get buffer
    let size := if fields.size.val < (fields.ptr - i 1).val then fields.ptr - i 1 else fields.size
    access.set buffer { fields with size }

-- UNTRANSLATED
-- Source: base/stream.jl:904-904 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:905-908 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function alloc_buf_hook(stream::LibuvStream, size::UInt)
    throttle = UInt(stream.throttle)
    return alloc_request(stream.buffer, (size > throttle) ? throttle : size)
end
```
-/
def allocBufferHook {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (allocate : Buffer → U → M World (Handle × I)) (stream : Stream) (size : U) : M World (Handle × I) := do
  let throttle ← JuliaLean.base.io.liftJl
    (JInt.convert (IntTy.u64.name) .u64 (← access.get stream).throttle.val)
  allocate (← access.get stream).buffer (if size.val > throttle.val then throttle else size)

-- UNTRANSLATED
-- Source: base/stream.jl:909-909 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:910-936 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_alloc_buf(handle::Ptr{Cvoid}, size::Csize_t, buf::Ptr{Cvoid})
    hd = uv_handle_data(handle)
    if hd == C_NULL
        ccall(:jl_uv_buf_set_len, Cvoid, (Ptr{Cvoid}, Csize_t), buf, 0)
        return nothing
    end
    stream = unsafe_pointer_to_objref(hd)::LibuvStream

    local data::Ptr{Cvoid}, newsize::Csize_t
    if stream.status != StatusActive
        data = C_NULL
        newsize = 0
    else
        (data, newsize) = alloc_buf_hook(stream, UInt(size))
        if data == C_NULL
            newsize = 0
        end
        # avoid aliasing of `nread` with `errno` in uv_readcb
        # or exceeding the Win32 maximum uv_buf_t len
        maxsize = @static Sys.iswindows() ? typemax(Cint) : typemax(Cssize_t)
        newsize > maxsize && (newsize = maxsize)
    end

    ccall(:jl_uv_buf_set_base, Cvoid, (Ptr{Cvoid}, Ptr{Cvoid}), buf, data)
    ccall(:jl_uv_buf_set_len, Cvoid, (Ptr{Cvoid}, Csize_t), buf, newsize)
    nothing
end
```
-/
def uvAllocBuffer {World Stream Condition : Type} (metadata : Metadata World Stream Condition)
    (handleData : Handle → M World Handle) (toStream : Handle → M World Stream)
    (allocate : Stream → U → M World (Handle × I))
    (setBase : Handle → Handle → M World Unit) (setLength : Handle → U → M World Unit)
    (windows : Bool) (handle : Handle) (size : U) (buffer : Handle) : M World Unit := do
  let data ← handleData handle
  if data.address.val = 0 then
    setLength buffer (u 0)
    return ()
  let stream ← toStream data
  let (data, size) ← if (← metadata.status stream).val != 4 then pure (nullHandle, u 0)
    else do
      let (data, count) ← allocate stream size
      let count ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 count.val)
      let count := if data.address.val = 0 then u 0 else count
      let maximum := u (if windows then 2^31 - 1 else 2^63 - 1)
      pure (data, if count.val > maximum.val then maximum else count)
  setBase buffer data
  setLength buffer size

-- UNTRANSLATED
-- Source: base/stream.jl:937-937 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:941-987 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function readcb_specialized(stream::LibuvStream, nread::Int, nrequested::UInt)
        lock(stream.cond)
        if nread < 0
            if nread == UV_ENOBUFS && nrequested == 0
                # remind the client that stream.buffer is full
                notify(stream.cond)
            elseif nread == UV_EOF # libuv called uv_stop_reading already
                if stream.status != StatusClosing
                    stream.status = StatusEOF
                    notify(stream.cond)
                    if stream isa TTY
                        # stream can still be used by reseteof (or possibly write)
                    elseif !(stream isa PipeEndpoint) && ccall(:uv_is_writable, Cint, (Ptr{Cvoid},), stream.handle) != 0
                        # stream can still be used by write
                    else
                        # underlying stream is no longer useful: begin finalization
                        ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), stream.handle)
                        stream.status = StatusClosing
                    end
                end
            else
                stream.readerror = _UVError("read", nread)
                notify(stream.cond)
                # This is a fatal connection error
                ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), stream.handle)
                stream.status = StatusClosing
            end
        else
            notify_filled(stream.buffer, nread)
            notify(stream.cond)
        end
        unlock(stream.cond)

        # Stop background reading when
        # 1) there's nobody paying attention to the data we are reading
        # 2) we have accumulated a lot of unread data OR
        # 3) we have an alternate buffer that has reached its limit.
        if stream.status == StatusPaused ||
           (stream.status == StatusActive &&
            ((bytesavailable(stream.buffer) >= stream.throttle) ||
             (bytesavailable(stream.buffer) >= stream.buffer.maxsize)))
            # save cycles by stopping kernel notifications from arriving
            ccall(:uv_read_stop, Cint, (Ptr{Cvoid},), stream)
            stream.status = StatusOpen
        end
        nothing
    end
```
-/
def readCallbackSpecialized {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (isTTY isPipe : Stream → Bool) (writable : Handle → M World CInt)
    (closeHandle : Handle → M World Unit) (readStop : Handle → M World CInt)
    (uvError : String → I → M World Error) (notifyFilled : Buffer → I → M World Unit)
    (noBuffers eofError : I) (stream : Stream) (readCount : I) (requested : U) : M World Unit := do
  ops.lock (← access.get stream).condition
  if readCount.val < 0 then
    if readCount.val = noBuffers.val && requested.val = 0 then
      ops.notify (← access.get stream).condition
    else if readCount.val = eofError.val then
      if (← access.get stream).status.val != 5 then
        access.set stream { (← access.get stream) with status := statusEOF }
        ops.notify (← access.get stream).condition
        if !isTTY stream then
          let canWrite ← if !isPipe stream then do
            pure ((← writable (← access.get stream).handle).val != 0)
            else pure false
          if !canWrite then
            closeHandle (← access.get stream).handle
            access.set stream { (← access.get stream) with status := statusClosing }
    else
      let error ← uvError "read" readCount
      access.set stream { (← access.get stream) with readerror := some error }
      ops.notify (← access.get stream).condition
      closeHandle (← access.get stream).handle
      access.set stream { (← access.get stream) with status := statusClosing }
  else
    notifyFilled (← access.get stream).buffer readCount
    ops.notify (← access.get stream).condition
  ops.unlock (← access.get stream).condition
  let stop ← if (← access.get stream).status.val = 8 then pure true
    else if (← access.get stream).status.val = 4 then do
      if (← buffers.available (← access.get stream).buffer).val ≥ (← access.get stream).throttle.val then pure true
      else pure ((← buffers.available (← access.get stream).buffer).val ≥ (← buffers.fields.get (← access.get stream).buffer).maxsize.val)
    else pure false
  if stop then
    let _ ← readStop (← access.get stream).handle
    access.set stream { (← access.get stream) with status := statusOpen }

/--
Julia source: base/stream.jl:2112-2114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function resolve(new::Nothing, oldstream, mode)
        (new=nothing, close=false, old=nothing)
    end
```
-/
def redirectResolveNothing {Stream : Type} (_old : Stream) (_mode : String) : Resolution Stream := .unchanged

/--
Julia source: base/stream.jl:2115-2117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function resolve(path::AbstractString, oldstream,mode)
        (new=open(path, mode), close=true, old=oldstream)
    end
```
-/
def redirectResolvePath {World Path Stream : Type} (openFile : Path → String → M World Stream)
    (path : Path) (old : Stream) (mode : String) : M World (Resolution Stream) := do
  pure (.owned (← openFile path mode) old)

/--
Julia source: base/stream.jl:2118-2120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function resolve(new, oldstream, mode)
        (new=new, close=false, old=oldstream)
    end
```
-/
def redirectResolveStream {Stream : Type} (stream old : Stream) (_mode : String) : Resolution Stream := .borrowed (some stream) old

/--
Julia source: base/stream.jl:2122-2122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    same_path(x, y) = false
```
-/
def redirectSamePathAny {A B : Type} (_left : A) (_right : B) : Bool := false

/--
Julia source: base/stream.jl:2123-2126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function same_path(x::AbstractString, y::AbstractString)
        # if x = y = "does_not_yet_exist.txt" then samefile will return false
        (abspath(x) == abspath(y)) || samefile(x,y)
    end
```
-/
def redirectSamePath {World Path Absolute : Type} (abspath : Path → M World Absolute)
    (equal : Absolute → Absolute → M World Bool) (samefile : Path → Path → M World Bool)
    (left right : Path) : M World Bool := do
  let leftAbsolute ← abspath left
  let rightAbsolute ← abspath right
  if ← equal leftAbsolute rightAbsolute then pure true else samefile left right

/--
Julia source: base/stream.jl:2303-2310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function wait_locked(s, buf, nb, tok)
        while bytesavailable(buf) < nb
            s.readerror === nothing || throw(s.readerror)
            isopen(s) || break
            s.status != StatusEOF || break
            wait_readnb(s, nb, tok)
        end
    end
```
-/
def bufferWaitReadLocked {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (isopen : Stream → M World Bool)
    (waitRead : Stream → I → Option Token → M World Unit)
    (stream : Stream) (buffer : Buffer) (count : I) (token : Option Token) : M World Unit :=
  JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
    if (← buffers.available buffer).val ≥ count.val then return .inl ()
    match (← access.get stream).readerror with
    | some error => throw error
    | none => pure ()
    if !(← isopen stream) then return .inl ()
    if (← access.get stream).status.val == 7 then return .inl ()
    waitRead stream count token
    pure (.inr ())) ()

/--
Julia source: base/stream.jl:938-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_readcb(handle::Ptr{Cvoid}, nread::Cssize_t, buf::Ptr{Cvoid})
    stream_unknown_type = @handle_as handle LibuvStream
    nrequested = ccall(:jl_uv_buf_len, Csize_t, (Ptr{Cvoid},), buf)
    function readcb_specialized(stream::LibuvStream, nread::Int, nrequested::UInt)
        lock(stream.cond)
        if nread < 0
            if nread == UV_ENOBUFS && nrequested == 0
                # remind the client that stream.buffer is full
                notify(stream.cond)
            elseif nread == UV_EOF # libuv called uv_stop_reading already
                if stream.status != StatusClosing
                    stream.status = StatusEOF
                    notify(stream.cond)
                    if stream isa TTY
                        # stream can still be used by reseteof (or possibly write)
                    elseif !(stream isa PipeEndpoint) && ccall(:uv_is_writable, Cint, (Ptr{Cvoid},), stream.handle) != 0
                        # stream can still be used by write
                    else
                        # underlying stream is no longer useful: begin finalization
                        ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), stream.handle)
                        stream.status = StatusClosing
                    end
                end
            else
                stream.readerror = _UVError("read", nread)
                notify(stream.cond)
                # This is a fatal connection error
                ccall(:jl_close_uv, Cvoid, (Ptr{Cvoid},), stream.handle)
                stream.status = StatusClosing
            end
        else
            notify_filled(stream.buffer, nread)
            notify(stream.cond)
        end
        unlock(stream.cond)

        # Stop background reading when
        # 1) there's nobody paying attention to the data we are reading
        # 2) we have accumulated a lot of unread data OR
        # 3) we have an alternate buffer that has reached its limit.
        if stream.status == StatusPaused ||
           (stream.status == StatusActive &&
            ((bytesavailable(stream.buffer) >= stream.throttle) ||
             (bytesavailable(stream.buffer) >= stream.buffer.maxsize)))
            # save cycles by stopping kernel notifications from arriving
            ccall(:uv_read_stop, Cint, (Ptr{Cvoid},), stream)
            stream.status = StatusOpen
        end
        nothing
    end
    readcb_specialized(stream_unknown_type, Int(nread), UInt(nrequested))
    nothing
end
```
-/
def uvReadCallback {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (handleAs : Handle → M World Stream) (bufferLength : Handle → M World U)
    (isTTY isPipe : Stream → Bool) (writable : Handle → M World CInt)
    (closeHandle : Handle → M World Unit) (readStop : Handle → M World CInt)
    (uvError : String → I → M World Error) (notifyFilled : Buffer → I → M World Unit)
    (noBuffers eofError : I) (handle : Handle) (readCount : I) (buffer : Handle) : M World Unit := do
  let stream ← handleAs handle
  let requested ← bufferLength buffer
  readCallbackSpecialized access buffers ops isTTY isPipe writable closeHandle readStop
    uvError notifyFilled noBuffers eofError stream (← JuliaLean.base.iostream.toInt readCount) requested

-- UNTRANSLATED
-- Source: base/stream.jl:991-991 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:992-999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reseteof(x::TTY)
    iolock_begin()
    if x.status == StatusEOF
        x.status = StatusOpen
    end
    iolock_end()
    nothing
end
```
-/
def resetTTYEOF {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (beginIO endIO : M World Unit) (reference : Ref) : M World Unit := do
  beginIO
  if (← metadata.status reference).val = 7 then metadata.setStatus reference statusOpen
  endIO

-- UNTRANSLATED
-- Source: base/stream.jl:1000-1000 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1001-1011 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uv_hook_close(uv::Union{LibuvStream, LibuvServer})
    lock(uv.cond)
    try
        uv.status = StatusClosed
        # notify any listeners that exist on this libuv stream type
        notify(uv.cond)
    finally
        unlock(uv.cond)
    end
    nothing
end
```
-/
def hookClose {World Ref Condition Token : Type} (metadata : Metadata World Ref Condition)
    (ops : ConditionOps World Condition Token) (reference : Ref) : M World Unit := do
  ops.lock (← metadata.condition reference)
  JuliaLean.base.io.finallyDo (do
    metadata.setStatus reference statusClosed
    ops.notify (← metadata.condition reference)) (do ops.unlock (← metadata.condition reference))

-- UNTRANSLATED
-- Source: base/stream.jl:1012-1047 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- ##########################################
-- # Pipe Abstraction
-- #  (composed of two half-pipes: .in and .out)
-- ##########################################
-- 
-- mutable struct Pipe <: AbstractPipe
--     in::PipeEndpoint # writable
--     out::PipeEndpoint # readable
-- end
-- 
-- """
--     Pipe()
-- 
-- Construct an uninitialized Pipe object, especially for IO communication between multiple processes.
-- 
-- The appropriate end of the pipe will be automatically initialized if the object is used in
-- process spawning. This can be useful to easily obtain references in process pipelines, e.g.:
-- 
-- ```
-- julia> err = Pipe()
-- 
-- # After this `err` will be initialized and you may read `foo`'s
-- # stderr from the `err` pipe, or pass `err` to other pipelines.
-- julia> run(pipeline(pipeline(`foo`, stderr=err), `cat`), wait=false)
-- 
-- # Now destroy the write half of the pipe, so that the read half will get EOF
-- julia> closewrite(err)
-- 
-- julia> read(err, String)
-- "stderr messages"
-- ```
-- 
-- See also [`Base.link_pipe!`](@ref).
-- """
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1048-1048 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Pipe() = Pipe(PipeEndpoint(), PipeEndpoint())
```
-/
def pipe {World Ref Endpoint : Type} (access : Access World Ref (Pipe Endpoint))
    (endpoint : M World Endpoint) : M World Ref := do
  let input ← endpoint
  let output ← endpoint
  access.new ⟨input, output⟩

/--
Julia source: base/stream.jl:1049-1049 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_reader(p::Pipe) = p.out
```
-/
def pipeReader {World Ref Endpoint : Type} (access : Access World Ref (Pipe Endpoint))
    (pipe : Ref) : M World Endpoint := do pure (← access.get pipe).output

/--
Julia source: base/stream.jl:1050-1050 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pipe_writer(p::Pipe) = p.in
```
-/
def pipeWriter {World Ref Endpoint : Type} (access : Access World Ref (Pipe Endpoint))
    (pipe : Ref) : M World Endpoint := do pure (← access.get pipe).input

-- UNTRANSLATED
-- Source: base/stream.jl:1051-1060 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     link_pipe!(pipe; reader_supports_async=false, writer_supports_async=false)
-- 
-- Initialize `pipe` and link the `in` endpoint to the `out` endpoint. The keyword
-- arguments `reader_supports_async`/`writer_supports_async` correspond to
-- `OVERLAPPED` on Windows and `O_NONBLOCK` on POSIX systems. They should be `true`
-- unless they'll be used by an external program (e.g. the output of a command
-- executed with [`run`](@ref)).
-- """
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1061-1066 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function link_pipe!(pipe::Pipe;
                    reader_supports_async = false,
                    writer_supports_async = false)
     link_pipe!(pipe.out, reader_supports_async, pipe.in, writer_supports_async)
     return pipe
end
```
-/
def linkPipe {World Ref Endpoint : Type} (access : Access World Ref (Pipe Endpoint))
    (link : Endpoint → Bool → Endpoint → Bool → M World Unit)
    (pipe : Ref) (readerAsync writerAsync : Bool) : M World Ref := do
  let reader := (← access.get pipe).output
  let writer := (← access.get pipe).input
  link reader readerAsync writer writerAsync
  pure pipe

-- UNTRANSLATED
-- Source: base/stream.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1068-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, stream::Pipe) = print(io,
    "Pipe(",
    _fd(stream.in), " ",
    uv_status_string(stream.in), " => ",
    _fd(stream.out), " ",
    uv_status_string(stream.out), ", ",
    bytesavailable(stream), " bytes waiting)")
```
-/
def showPipe {World Ref Endpoint Out FD : Type} (access : Access World Ref (Pipe Endpoint))
    (fd : Endpoint → M World FD) (status : Endpoint → M World String) (available : Ref → M World I)
    (print : Out → List (ShowArg Unit FD) → M World Unit) (out : Out) (pipe : Ref) : M World Unit := do
  let input ← fd (← access.get pipe).input
  let inputStatus ← status (← access.get pipe).input
  let output ← fd (← access.get pipe).output
  let outputStatus ← status (← access.get pipe).output
  let count ← available pipe
  print out [.text "Pipe(", .descriptor input, .text " ", .text inputStatus, .text " => ",
    .descriptor output, .text " ", .text outputStatus, .text ", ", .count count, .text " bytes waiting)"]

-- UNTRANSLATED
-- Source: base/stream.jl:1075-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1076-1076 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
closewrite(pipe::Pipe) = close(pipe.in)
```
-/
def closewritePipe {World Ref Endpoint : Type} (access : Access World Ref (Pipe Endpoint))
    (close : Endpoint → M World Unit) (pipe : Ref) : M World Unit := do close (← access.get pipe).input

-- UNTRANSLATED
-- Source: base/stream.jl:1077-1079 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## Functions for PipeEndpoint and PipeServer ##
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1080-1090 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function open_pipe!(p::PipeEndpoint, handle::OS_HANDLE)
    iolock_begin()
    if p.status != StatusInit
        error("pipe is already in use or has been closed")
    end
    err = ccall(:uv_pipe_open, Int32, (Ptr{Cvoid}, OS_HANDLE), p.handle, handle)
    uv_error("pipe_open", err)
    p.status = StatusOpen
    iolock_end()
    return p
end
```
-/
def openPipe {World Endpoint Condition FD : Type} (metadata : Metadata World Endpoint Condition)
    (beginIO endIO : M World Unit) (openPipe : Handle → FD → M World CInt)
    (uvError : String → CInt → M World Unit) (endpoint : Endpoint) (handle : FD) : M World Endpoint := do
  beginIO
  if (← metadata.status endpoint).val != 1 then
    throw (.errorException "pipe is already in use or has been closed")
  let status ← openPipe (← metadata.handle endpoint) handle
  uvError "pipe_open" status
  metadata.setStatus endpoint statusOpen
  endIO
  pure endpoint

-- UNTRANSLATED
-- Source: base/stream.jl:1091-1092 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1093-1109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function link_pipe!(read_end::PipeEndpoint, reader_supports_async::Bool,
                    write_end::PipeEndpoint, writer_supports_async::Bool)
    rd, wr = link_pipe(reader_supports_async, writer_supports_async)
    try
        try
            open_pipe!(read_end, rd)
        catch
            close_pipe_sync(rd)
            rethrow()
        end
        open_pipe!(write_end, wr)
    catch
        close_pipe_sync(wr)
        rethrow()
    end
    nothing
end
```
-/
def linkEndpoints {World Endpoint FD : Type}
    (link : Bool → Bool → M World (FD × FD))
    (openPipe : Endpoint → FD → M World Endpoint) (closeSync : FD → M World Unit)
    (reader : Endpoint) (readerAsync : Bool) (writer : Endpoint) (writerAsync : Bool) : M World Unit := do
  let (readFD, writeFD) ← link readerAsync writerAsync
  tryCatch (do
    tryCatch (do let _ ← openPipe reader readFD; pure ()) (fun error => do
      closeSync readFD
      throw error)
    let _ ← openPipe writer writeFD
    pure ()) (fun error => do
      closeSync writeFD
      throw error)

-- UNTRANSLATED
-- Source: base/stream.jl:1110-1110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1111-1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function link_pipe(reader_supports_async::Bool, writer_supports_async::Bool)
    UV_NONBLOCK_PIPE = 0x40
    fildes = Ref{Pair{OS_HANDLE, OS_HANDLE}}(INVALID_OS_HANDLE => INVALID_OS_HANDLE) # read (in) => write (out)
    err = ccall(:uv_pipe, Int32, (Ptr{Pair{OS_HANDLE, OS_HANDLE}}, Cint, Cint),
                fildes,
                reader_supports_async * UV_NONBLOCK_PIPE,
                writer_supports_async * UV_NONBLOCK_PIPE)
    uv_error("pipe", err)
    return fildes[]
end
```
-/
def linkPipeFD {World FD Ref : Type} (invalid : FD)
    (newRef : FD × FD → M World Ref) (getRef : Ref → M World (FD × FD))
    (uvPipe : Ref → CInt → CInt → M World CInt) (uvError : String → CInt → M World Unit)
    (readerAsync writerAsync : Bool) : M World (FD × FD) := do
  let reference ← newRef (invalid, invalid)
  let result ← uvPipe reference (cint (if readerAsync then 64 else 0)) (cint (if writerAsync then 64 else 0))
  uvError "pipe" result
  getRef reference

-- UNTRANSLATED
-- Source: base/stream.jl:1121-1122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if Sys.iswindows()
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1123-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function close_pipe_sync(handle::WindowsRawSocket)
        ccall(:CloseHandle, stdcall, Cint, (WindowsRawSocket,), handle)
        nothing
    end
```
-/
def closePipeWindows {World FD : Type} (closeHandle : FD → M World CInt) (handle : FD) : M World Unit := do
  let _ ← closeHandle handle
  pure ()

-- UNTRANSLATED
-- Source: base/stream.jl:1127-1127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- else
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1128-1131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function close_pipe_sync(handle::RawFD)
        ccall(:close, Cint, (RawFD,), handle)
        nothing
    end
```
-/
def closePipePOSIX {World FD : Type} (close : FD → M World CInt) (handle : FD) : M World Unit := do
  let _ ← close handle
  pure ()

-- UNTRANSLATED
-- Source: base/stream.jl:1132-1137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- ## Functions for any LibuvStream ##
-- 
-- # flow control
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1138-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function start_reading(stream::LibuvStream)
    iolock_begin()
    if stream.status == StatusOpen
        if !isreadable(stream)
            error("tried to read a stream that is not readable")
        end
        # libuv may call the alloc callback immediately
        # for a TTY on Windows, so ensure the status is set first
        stream.status = StatusActive
        ret = ccall(:uv_read_start, Cint, (Ptr{Cvoid}, Ptr{Cvoid}, Ptr{Cvoid}),
                    stream, @cfunction(uv_alloc_buf, Cvoid, (Ptr{Cvoid}, Csize_t, Ptr{Cvoid})),
                    @cfunction(uv_readcb, Cvoid, (Ptr{Cvoid}, Cssize_t, Ptr{Cvoid})))
    elseif stream.status == StatusPaused
        stream.status = StatusActive
        ret = Int32(0)
    elseif stream.status == StatusActive
        ret = Int32(0)
    else
        ret = Int32(-1)
    end
    iolock_end()
    return ret
end
```
-/
def startReading {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (beginIO endIO : M World Unit) (readable : Ref → M World Bool)
    (readStart : Ref → M World CInt) (reference : Ref) : M World CInt := do
  beginIO
  let result ← if (← metadata.status reference).val = 3 then do
    if !(← readable reference) then throw (.errorException "tried to read a stream that is not readable")
    metadata.setStatus reference statusActive
    readStart reference
    else if (← metadata.status reference).val = 8 then do
      metadata.setStatus reference statusActive
      pure (cint 0)
    else if (← metadata.status reference).val = 4 then pure (cint 0)
    else pure (cint (-1))
  endIO
  pure result

-- UNTRANSLATED
-- Source: base/stream.jl:1161-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- if Sys.iswindows()
--     # the low performance version of stop_reading is required
--     # on Windows due to an NT kernel bug that we can't use a blocking
--     # stream for non-blocking (overlapped) calls,
--     # and a ReadFile call blocking on one thread
--     # causes all other operations on that stream to lockup
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1168-1176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function stop_reading(stream::LibuvStream)
        iolock_begin()
        if stream.status == StatusActive
            stream.status = StatusOpen
            ccall(:uv_read_stop, Cint, (Ptr{Cvoid},), stream)
        end
        iolock_end()
        nothing
    end
```
-/
def stopReadingWindows {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (beginIO endIO : M World Unit) (readStop : Ref → M World CInt) (reference : Ref) : M World Unit := do
  beginIO
  if (← metadata.status reference).val = 4 then
    metadata.setStatus reference statusOpen
    let _ ← readStop reference
  endIO

-- UNTRANSLATED
-- Source: base/stream.jl:1177-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- else
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1178-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function stop_reading(stream::LibuvStream)
        iolock_begin()
        if stream.status == StatusActive
            stream.status = StatusPaused
        end
        iolock_end()
        nothing
    end
```
-/
def stopReadingPOSIX {World Ref Condition : Type} (metadata : Metadata World Ref Condition)
    (beginIO endIO : M World Unit) (reference : Ref) : M World Unit := do
  beginIO
  if (← metadata.status reference).val = 4 then metadata.setStatus reference statusPaused
  endIO

-- UNTRANSLATED
-- Source: base/stream.jl:1186-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- # bulk read / write
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1190-1190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
readbytes!(s::LibuvStream, a::Vector{UInt8}, nb = length(a)) = readbytes!(s, a, Int(nb))
```
-/
def readbytesConvert {World Stream Vector N : Type}
    (toInt : N → M World I) (readbytes : Stream → Vector → I → M World I)
    (stream : Stream) (array : Vector) (count : N) : M World I := do
  readbytes stream array (← toInt count)

-- Source: base/stream.jl:1231-1231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/stream.jl:1198-1207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function wait_locked(s, buf, nb, tok)
        while bytesavailable(buf) < nb
            s.readerror === nothing || throw(s.readerror)
            isopen(s) || break
            s.status != StatusEOF || break
            iolock_end()
            wait_readnb(s, nb, tok)
            iolock_begin()
        end
    end
```
-/
def waitReadLocked {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (isopen : Stream → M World Bool)
    (beginIO endIO : M World Unit) (waitRead : Stream → I → Option Token → M World Unit)
    (stream : Stream) (buffer : Buffer) (count : I) (token : Option Token) : M World Unit :=
  JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
    if (← buffers.available buffer).val ≥ count.val then return .inl ()
    match (← access.get stream).readerror with
    | some error => throw error
    | none => pure ()
    if !(← isopen stream) then return .inl ()
    if (← access.get stream).status.val == 7 then return .inl ()
    endIO
    waitRead stream count token
    beginIO
    pure (.inr ())) ()

/--
Julia source: base/stream.jl:1191-1230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readbytes!(s::LibuvStream, a::Vector{UInt8}, nb::Int; cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    iolock_begin()
    sbuf = s.buffer
    @assert sbuf.seekable == false "buffer should not be seekable"
    @assert sbuf.maxsize >= nb "insufficient buffer size"

    function wait_locked(s, buf, nb, tok)
        while bytesavailable(buf) < nb
            s.readerror === nothing || throw(s.readerror)
            isopen(s) || break
            s.status != StatusEOF || break
            iolock_end()
            wait_readnb(s, nb, tok)
            iolock_begin()
        end
    end

    if nb <= SZ_UNBUFFERED_IO # Under this limit we are OK with copying the array from the stream's buffer
        wait_locked(s, sbuf, nb, tok)
    end
    if bytesavailable(sbuf) >= nb
        nread = readbytes!(sbuf, a, nb)
    else
        initsize = length(a)
        newbuf = _truncated_pipebuffer(a; maxsize=nb)
        nread = try
            s.buffer = newbuf
            write(newbuf, sbuf)
            wait_locked(s, newbuf, nb, tok)
            bytesavailable(newbuf)
        finally
            s.buffer = sbuf
        end
        _take!(a, _unsafe_take!(newbuf))
        length(a) >= initsize || resize!(a, initsize)
    end
    iolock_end()
    return nread
end
```
-/
def readbytes {World Stream Buffer Condition Lock Vector Data Token Taken : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data)
    (precheck : CancelArg Token → M World (CancelArg Token)) (resolve : CancelArg Token → M World (Option Token))
    (beginIO endIO : M World Unit) (isopen : Stream → M World Bool)
    (waitRead : Stream → I → Option Token → M World Unit)
    (length : Vector → M World I) (truncatePipe : Vector → I → M World Buffer)
    (writeBuffer : Buffer → Buffer → M World I) (unsafeTake : Buffer → M World Taken)
    (takeInto : Vector → Taken → M World Unit) (resize : Vector → I → M World Unit)
    (stream : Stream) (array : Vector) (count : I) (cancel : CancelArg Token) : M World I := do
  let token ← resolve (← precheck cancel)
  beginIO
  let buffer := (← access.get stream).buffer
  if (← buffers.fields.get buffer).seekable then throw (.foreignError "AssertionError" "buffer should not be seekable")
  if (← buffers.fields.get buffer).maxsize.val < count.val then throw (.foreignError "AssertionError" "insufficient buffer size")
  if count.val ≤ JuliaLean.base.io.szUnbufferedIO.val then
    waitReadLocked access buffers isopen beginIO endIO waitRead stream buffer count token
  let result ← if (← buffers.available buffer).val ≥ count.val then buffers.readbytes buffer array count
    else do
      let initialSize ← length array
      let newBuffer ← truncatePipe array count
      let count ← JuliaLean.base.io.finallyDo (do
        access.set stream { (← access.get stream) with buffer := newBuffer }
        let _ ← writeBuffer newBuffer buffer
        waitReadLocked access buffers isopen beginIO endIO waitRead stream newBuffer count token
        buffers.available newBuffer)
        (do access.set stream { (← access.get stream) with buffer })
      takeInto array (← unsafeTake newBuffer)
      if (← length array).val < initialSize.val then resize array initialSize
      pure count
  endIO
  pure result


/--
Julia source: base/stream.jl:1232-1238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(stream::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    wait_readnb(stream, typemax(Int), resolve_cancel_token(precheck_cancel_arg(cancel)))
    iolock_begin()
    bytes = take!(stream.buffer)
    iolock_end()
    return bytes
end
```
-/
def readAll {World Stream Buffer Condition Lock Vector Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitRead : Stream → I → Option Token → M World Unit)
    (beginIO endIO : M World Unit) (take : Buffer → M World Vector)
    (stream : Stream) (cancel : CancelArg Token) : M World Vector := do
  let token ← resolve (← precheck cancel)
  waitRead stream (JInt.typemax .i64) token
  beginIO
  let bytes ← take (← access.get stream).buffer
  endIO
  pure bytes

-- Source: base/stream.jl:1239-1239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/stream.jl:1276-1276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/stream.jl:1247-1256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function wait_locked(s, buf, nb, tok)
        while bytesavailable(buf) < nb
            s.readerror === nothing || throw(s.readerror)
            isopen(s) || throw(EOFError())
            s.status != StatusEOF || throw(EOFError())
            iolock_end()
            wait_readnb(s, nb, tok)
            iolock_begin()
        end
    end
```
-/
def waitUnsafeReadLocked {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (isopen : Stream → M World Bool)
    (beginIO endIO : M World Unit) (waitRead : Stream → I → Option Token → M World Unit)
    (stream : Stream) (buffer : Buffer) (count : I) (token : Option Token) : M World Unit :=
  JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
    if (← buffers.available buffer).val ≥ count.val then return .inl ()
    match (← access.get stream).readerror with
    | some error => throw error
    | none => pure ()
    if !(← isopen stream) then throw .eofError
    if (← access.get stream).status.val == 7 then throw .eofError
    endIO
    waitRead stream count token
    beginIO
    pure (.inr ())) ()

/--
Julia source: base/stream.jl:1240-1275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_read(s::LibuvStream, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    iolock_begin()
    sbuf = s.buffer
    @assert sbuf.seekable == false "buffer should not be seekable"
    @assert sbuf.maxsize >= nb "insufficient buffer size"

    function wait_locked(s, buf, nb, tok)
        while bytesavailable(buf) < nb
            s.readerror === nothing || throw(s.readerror)
            isopen(s) || throw(EOFError())
            s.status != StatusEOF || throw(EOFError())
            iolock_end()
            wait_readnb(s, nb, tok)
            iolock_begin()
        end
    end

    if nb <= SZ_UNBUFFERED_IO # Under this limit we are OK with copying the array from the stream's buffer
        wait_locked(s, sbuf, Int(nb), tok)
    end
    if bytesavailable(sbuf) >= nb
        unsafe_read(sbuf, p, nb)
    else
        newbuf = _truncated_pipebuffer(unsafe_wrap(Array, p, nb); maxsize=Int(nb))
        try
            s.buffer = newbuf
            write(newbuf, sbuf)
            wait_locked(s, newbuf, Int(nb), tok)
        finally
            s.buffer = sbuf
        end
    end
    iolock_end()
    nothing
end
```
-/
def unsafeRead {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data)
    (precheck : CancelArg Token → M World (CancelArg Token)) (resolve : CancelArg Token → M World (Option Token))
    (beginIO endIO : M World Unit) (isopen : Stream → M World Bool)
    (waitRead : Stream → I → Option Token → M World Unit)
    (unsafeWrap : BytePointer → U → M World Vector) (truncatePipe : Vector → I → M World Buffer)
    (writeBuffer : Buffer → Buffer → M World I)
    (stream : Stream) (pointer : BytePointer) (count : U) (cancel : CancelArg Token) : M World Unit := do
  let token ← resolve (← precheck cancel)
  beginIO
  let buffer := (← access.get stream).buffer
  if (← buffers.fields.get buffer).seekable then throw (.foreignError "AssertionError" "buffer should not be seekable")
  if (← buffers.fields.get buffer).maxsize.val < count.val then throw (.foreignError "AssertionError" "insufficient buffer size")
  if count.val ≤ JuliaLean.base.io.szUnbufferedIO.val then
    waitUnsafeReadLocked access buffers isopen beginIO endIO waitRead stream buffer (← JuliaLean.base.iostream.toInt count) token
  if (← buffers.available buffer).val ≥ count.val then buffers.unsafeRead buffer pointer count
  else
    let wrapped ← unsafeWrap pointer count
    let newBuffer ← truncatePipe wrapped (← JuliaLean.base.iostream.toInt count)
    JuliaLean.base.io.finallyDo (do
      access.set stream { (← access.get stream) with buffer := newBuffer }
      let _ ← writeBuffer newBuffer buffer
      waitUnsafeReadLocked access buffers isopen beginIO endIO waitRead stream newBuffer (← JuliaLean.base.iostream.toInt count) token)
      (do access.set stream { (← access.get stream) with buffer })
  endIO


/--
Julia source: base/stream.jl:1277-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(this::LibuvStream, ::Type{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    iolock_begin()
    sbuf = this.buffer
    @assert sbuf.seekable == false "buffer should not be seekable"
    while bytesavailable(sbuf) < 1
        iolock_end()
        eof(this; cancel) && throw(EOFError())
        iolock_begin()
    end
    c = read(sbuf, UInt8)
    iolock_end()
    return c
end
```
-/
def readByte {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (beginIO endIO : M World Unit) (eof : Stream → CancelArg Token → M World Bool)
    (stream : Stream) (cancel : CancelArg Token) : M World Byte := do
  let cancel ← precheck cancel
  beginIO
  let buffer := (← access.get stream).buffer
  if (← buffers.fields.get buffer).seekable then
    throw (.foreignError "AssertionError" "buffer should not be seekable")
  JuliaLean.base.io.whileLoop (fun _ : Unit => do
    if (← buffers.available buffer).val ≥ 1 then return .inl ()
    endIO
    if ← eof stream cancel then throw .eofError
    beginIO
    pure (.inr ())) ()
  let value ← buffers.readByte buffer
  endIO
  pure value

-- UNTRANSLATED
-- Source: base/stream.jl:1291-1291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1292-1300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readavailable(this::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    wait_readnb(this, 1, resolve_cancel_token(precheck_cancel_arg(cancel))) # unlike the other `read` family of functions, this one doesn't guarantee error reporting
    iolock_begin()
    buf = this.buffer
    @assert buf.seekable == false "buffer should not be seekable"
    bytes = take!(buf)
    iolock_end()
    return bytes
end
```
-/
def readavailable {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitRead : Stream → I → Option Token → M World Unit)
    (beginIO endIO : M World Unit) (stream : Stream) (cancel : CancelArg Token) : M World Vector := do
  let token ← resolve (← precheck cancel)
  waitRead stream (i 1) token
  beginIO
  let buffer := (← access.get stream).buffer
  if (← buffers.fields.get buffer).seekable then
    throw (.foreignError "AssertionError" "buffer should not be seekable")
  let bytes ← buffers.take buffer
  endIO
  pure bytes

-- Source: base/stream.jl:1301-1301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/stream.jl:1346-1346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/stream.jl:1302-1345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyuntil(out::IO, x::LibuvStream, c::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    iolock_begin()
    buf = x.buffer
    @assert buf.seekable == false "buffer should not be seekable"
    if !occursin(c, buf) # fast path checks first
        x.readerror === nothing || throw(x.readerror)
        if isopen(x) && x.status != StatusEOF
            preserve_handle(x)
            lock(x.cond)
            locked = true
            try
                while !occursin(c, x.buffer)
                    x.readerror === nothing || throw(x.readerror)
                    isopen(x) || break
                    x.status != StatusEOF || break
                    start_reading(x) # ensure we are reading
                    iolock_end()
                    locked = false
                    wait(x.cond, tok)
                    locked = true
                    unlock(x.cond)
                    locked = false
                    iolock_begin()
                    lock(x.cond)
                    locked = true
                end
            finally
                # see wait_readnb's teardown note
                locked || lock(x.cond)
                if isempty(x.cond)
                    stop_reading(x) # stop reading iff there are currently no other read clients of the stream
                end
                unlock(x.cond)
                unpreserve_handle(x)
            end
        end
    end
    # thread the resolved token (or explicit shield): the in-memory copy's
    # write to `out` is itself token-gated
    copyuntil(out, buf, c; keep, cancel=tok)
    iolock_end()
    return out
end
```
-/
def copyuntil {World Out Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token)) (resolve : CancelArg Token → M World (Option Token))
    (isopen : Stream → M World Bool) (beginIO endIO : M World Unit)
    (preserve unpreserve : Stream → M World Unit) (empty : Condition → M World Bool)
    (startReading : Stream → M World CInt) (stopReading : Stream → M World Unit)
    (copyBuffer : Out → Buffer → Byte → Bool → CancelArg Token → M World Out)
    (out : Out) (stream : Stream) (delimiter : Byte) (keep : Bool) (cancel : CancelArg Token) : M World Out := do
  let token ← resolve (← precheck cancel)
  beginIO
  let buffer := (← access.get stream).buffer
  if (← buffers.fields.get buffer).seekable then throw (.foreignError "AssertionError" "buffer should not be seekable")
  if !(← buffers.occursin delimiter buffer) then
    match (← access.get stream).readerror with
    | some error => throw error
    | none => pure ()
    let readable ← if ← isopen stream then pure ((← access.get stream).status.val != 7) else pure false
    if readable then
      preserve stream
      ops.lock (← access.get stream).condition
      JuliaLean.base.locks_mt.runFrame true (JuliaLean.base.io.finallyDo (do
        JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
          if ← JuliaLean.base.locks_mt.liftFrame (do buffers.occursin delimiter (← access.get stream).buffer) then return .inl ()
          match (← JuliaLean.base.locks_mt.liftFrame (access.get stream)).readerror with
          | some error => throw error
          | none => pure ()
          if !(← JuliaLean.base.locks_mt.liftFrame (isopen stream)) then return .inl ()
          if (← JuliaLean.base.locks_mt.liftFrame (access.get stream)).status.val == 7 then return .inl ()
          let _ ← JuliaLean.base.locks_mt.liftFrame (startReading stream)
          JuliaLean.base.locks_mt.liftFrame endIO
          JuliaLean.base.locks_mt.setFrame false
          JuliaLean.base.locks_mt.liftFrame (do ops.wait (← access.get stream).condition token)
          JuliaLean.base.locks_mt.setFrame true
          JuliaLean.base.locks_mt.liftFrame (do ops.unlock (← access.get stream).condition)
          JuliaLean.base.locks_mt.setFrame false
          JuliaLean.base.locks_mt.liftFrame beginIO
          JuliaLean.base.locks_mt.liftFrame (do ops.lock (← access.get stream).condition)
          JuliaLean.base.locks_mt.setFrame true
          pure (.inr ())) ()) (do
            if !(← JuliaLean.base.locks_mt.getFrame) then JuliaLean.base.locks_mt.liftFrame (do ops.lock (← access.get stream).condition)
            if ← JuliaLean.base.locks_mt.liftFrame (do empty (← access.get stream).condition) then
              JuliaLean.base.locks_mt.liftFrame (stopReading stream)
            JuliaLean.base.locks_mt.liftFrame (do ops.unlock (← access.get stream).condition)
            JuliaLean.base.locks_mt.liftFrame (unpreserve stream)))
  let _ ← copyBuffer out buffer delimiter keep (.explicit token)
  endIO
  pure out


/--
Julia source: base/stream.jl:1347-1349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uv_write(s::LibuvStream, p::Vector{UInt8}, cancel::CancelTokenArg=DEFAULT_CANCEL,
         partial::Bool=false) =
    GC.@preserve p _uv_write_owned(s, pointer(p), UInt(sizeof(p)), cancel, p, partial)
```
-/
def uvWriteVector {World Stream Vector Token : Type}
    (pointer : Vector → M World BytePointer) (sizeof : Vector → M World I)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option Vector → Bool → M World I)
    (stream : Stream) (array : Vector) (cancel : CancelArg Token) (partialWrite : Bool) : M World I := do
  let pointer ← pointer array
  let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof array).val)
  writeOwned stream pointer size cancel (some array) partialWrite

-- Source: base/stream.jl:1350-1359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Issue the write and wait for its completion, delivering a cancellation of
-- # `tok` by interrupting the wait. A cancelled wait first resolves the
-- # in-flight request per the severity (SAFE awaits the completion callback,
-- # so the buffer is provably out of OS hands); then, with `partial` unset,
-- # the CancellationRequest is thrown - bytes already accepted stay written -
-- # and with `partial` set the count of accepted bytes is returned and the
-- # (level-triggered) cancellation is left to the caller's next cancellation
-- # point. The caller must have acquired the iolock, which is released before
-- # returning.
-- /Source

-- Source: base/stream.jl:1465-1477 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Resolve the ownership of a cancelled write's uv request(s) and return the
-- # partial write count: the last chunk's for a single-request write, the
-- # exact total of accepted bytes for a split one (0 for whatever had to be
-- # detached without awaiting completion). Every in-flight request is
-- # `uv_cancel`ed, tail-first for a split write: our chunks sit contiguously
-- # in the stream's queue, so cancelling from the tail dequeues behind the
-- # still-active head and the wire always keeps a clean prefix. For SAFE
-- # cancellations this awaits the completion callback(s), so the caller's
-- # buffer is provably no longer in use by the OS when this returns; only a
-- # severity escalation interrupts that bounded wait. Enters with the iolock
-- # released at the sigatomic level of the interrupted wait; unwinds both and
-- # the handle preservation.
-- /Source

-- Source: base/stream.jl:1556-1557 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Whether every request of a split write has completed (data == C_NULL).
-- /Source


/--
Julia source: base/stream.jl:1558-1564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _split_complete(uvw::Ptr{Cvoid}, others::Vector{Ptr{Cvoid}})
    uv_req_data(uvw) == C_NULL || return false
    for r in others
        uv_req_data(r) == C_NULL || return false
    end
    return true
end
```
-/
def splitComplete {World : Type} (getData : Handle → M World Handle)
    (request : Handle) (others : List Handle) : M World Bool := do
  if (← getData request).address.val != 0 then return false
  for request in others do
    if (← getData request).address.val != 0 then return false
  pure true

-- Source: base/stream.jl:1565-1575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Split-write counterpart of _end_uvreq_wait! (caller holds the iolock, at
-- # the sigatomic level of the wait): resolve the ownership of every chunk
-- # request and return the total of the completed ones' accepted-byte counts.
-- # Completed requests (data == C_NULL) are summed and freed; in-flight ones
-- # are detached for their callbacks to free - `uv_cancel`ed first, tail-first
-- # (last request first, then earlier chunks in reverse submission order, so
-- # the queue keeps a clean prefix), when `trycancel` is set - with `owner`
-- # kept rooted under each until its callback runs. Then unwinds the witness,
-- # the registration, the iolock, the sigatomic section, and the handle
-- # preservation, exactly like _end_uvreq_wait!.
-- /Source

-- Source: base/stream.jl:1603-1603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


/--
Julia source: base/stream.jl:1604-1607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_write(s::LibuvStream, p::Ptr{UInt8}, n::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL,
                  owner=nothing)
    return _uv_write_owned(s, p, n, cancel, owner, false)
end
```
-/
def uvWrite {World Stream Owner Token : Type}
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option Owner → Bool → M World I)
    (stream : Stream) (pointer : BytePointer) (count : U) (cancel : CancelArg Token)
    (owner : Option Owner) : M World I := writeOwned stream pointer count cancel owner false

-- UNTRANSLATED
-- Source: base/stream.jl:1608-1610 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Positional core of uv_write: an `owner::Any` keyword call is not statically
-- # resolvable (the NamedTuple type is abstract), which breaks trimmed builds.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1611-1625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uv_write_owned(s::LibuvStream, p::Ptr{UInt8}, n::UInt, cancel::CancelTokenArg,
                         @nospecialize(owner), partial::Bool)
    tok = resolve_cancel_token(cancel)
    # branch on the token explicitly: a Union-typed `tok` alongside the
    # deliberately unspecialized `owner` leaves the callee unresolvable
    # for trimmed builds
    nb = tok === nothing ? _uv_write_wait(s, p, n, nothing, owner, partial) :
                           _uv_write_wait(s, p, n, tok, owner, partial)
    # With `partial` set, nb < n means the wait was cancelled: the write
    # reports the count of accepted bytes (like a short write) and the
    # cancellation itself is delivered at the caller's next cancellation
    # point - level-triggered, nothing is lost by returning normally here.
    # Without it, a cancelled wait has already thrown.
    return nb
end
```
-/
def uvWriteOwned {World Stream Owner Token : Type}
    (resolve : CancelArg Token → M World (Option Token))
    (writeWait : Stream → BytePointer → U → Option Token → Option Owner → Bool → M World I)
    (stream : Stream) (pointer : BytePointer) (count : U) (cancel : CancelArg Token)
    (owner : Option Owner) (partialWrite : Bool) : M World I := do
  let token ← resolve cancel
  let count ← match token with
    | none => writeWait stream pointer count none owner partialWrite
    | some token => writeWait stream pointer count (some token) owner partialWrite
  pure count

-- UNTRANSLATED
-- Source: base/stream.jl:1626-1633 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # helper function for uv_write that submits the write as one request per
-- # OS-sized chunk rather than waiting, caller must hold the iolock. Returns
-- # the last chunk's uv_write_t, that chunk's size, and - for split writes -
-- # the vector of the earlier chunks' requests (nothing for the common
-- # single-request case). All requests go out with data C_NULL
-- # (fire-and-forget); a waiter that wants completion re-points them at its
-- # wait entry under the same iolock hold (see _uv_write_wait).
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1634-1662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_write_async(s::LibuvStream, p::Ptr{UInt8}, n::UInt, chunk::UInt=MAX_OS_WRITE)
    check_open(s)
    others = nothing
    while true
        uvw = Libc.malloc(_sizeof_uv_write)
        uv_req_set_data(uvw, C_NULL) # in case we get interrupted before arriving at the wait call
        nwrite = min(n, chunk) # split up the write into chunks the OS can handle.
        # TODO: use writev instead of a loop (requires libuv to bound the
        # per-syscall submission: as of now it recombines all bufs of a
        # request into one writev/WSASend, blowing through the OS limits
        # this chunking exists to respect)
        err = ccall(:jl_uv_write,
                    Int32,
                    (Ptr{Cvoid}, Ptr{Cvoid}, UInt, Ptr{Cvoid}, Ptr{Cvoid}),
                    s, p, nwrite, uvw,
                    @cfunction(uv_writecb_task, Cvoid, (Ptr{Cvoid}, Cint)))
        if err < 0
            Libc.free(uvw)
            uv_error("write", err)
        end
        n -= nwrite
        p += nwrite
        if n == 0
            return uvw, nwrite, others
        end
        others === nothing && (others = Ptr{Cvoid}[])
        push!(others::Vector{Ptr{Cvoid}}, uvw)
    end
end
```
-/
def uvWriteAsync {World Stream : Type} (checkOpen : Stream → M World Unit)
    (allocate : M World Handle) (setData : Handle → Handle → M World Unit)
    (writeRequest : Stream → BytePointer → U → Handle → Handle → M World CInt)
    (callback : Handle) (free : Handle → M World Unit)
    (uvError : String → CInt → M World Unit) (stream : Stream) (pointer : BytePointer)
    (count chunk : U) : M World (Handle × U × Option (List Handle)) := do
  checkOpen stream
  JuliaLean.base.io.whileLoop
    (fun ((pointer, count, others) : BytePointer × U × Option (List Handle)) => do
      let request ← allocate
      setData request nullHandle
      let written := if count.val < chunk.val then count else chunk
      let error ← writeRequest stream pointer written request callback
      if error.val < 0 then
        free request
        uvError "write" error
      let count := count - written
      let pointer := JuliaLean.base.pointer.ptrAddInteger (fun x : U => x) pointer written
      if count.val = 0 then return .inl (request, written, others)
      let others := some (others.getD [] ++ [request])
      return .inr (pointer, count, others)) (pointer, count, none)

-- UNTRANSLATED
-- Source: base/stream.jl:1663-1668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- # Optimized send
-- # - smaller writes are buffered, final uv write on flush or when buffer full
-- # - large isbits arrays are unbuffered and written directly
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1669-1677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::LibuvStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    # Like the generic unsafe_write fallback below, but carrying the buffer's
    # owner so a detached (abandoned) write keeps it rooted; see
    # _detached_uvreq_roots.
    GC.@preserve a begin
        return Int(_unsafe_write_owned(s, pointer(a), UInt(sizeof(a)), cancel, a, false))
    end
end
```
-/
def writeOwnedVector {World Stream A Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option A → Bool → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  let cancel ← precheck cancel
  let pointer ← pointer value
  let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
  JuliaLean.base.iostream.toInt (← writeOwned stream pointer size cancel (some value) false)

-- UNTRANSLATED
-- Source: base/stream.jl:1678-1678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1679-1684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writepartial(s::LibuvStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    GC.@preserve a begin
        return Int(_unsafe_write_owned(s, pointer(a), UInt(sizeof(a)), cancel, a, true))
    end
end
```
-/
def writePartialOwnedVector {World Stream A Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option A → Bool → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  let cancel ← precheck cancel
  let pointer ← pointer value
  let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
  JuliaLean.base.iostream.toInt (← writeOwned stream pointer size cancel (some value) true)

-- UNTRANSLATED
-- Source: base/stream.jl:1685-1690 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # The public String path must be owner-carrying for the same reason: the
-- # generic method (strings/io.jl) preserves the string only until
-- # unsafe_write returns, but an abandoning cancellation can detach the
-- # in-flight request, which then references the string until its completion
-- # callback runs.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

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
-/
def writeOwnedString {World Stream A Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option A → Bool → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  let cancel ← precheck cancel
  let pointer ← pointer value
  let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
  JuliaLean.base.iostream.toInt (← writeOwned stream pointer size cancel (some value) false)

-- UNTRANSLATED
-- Source: base/stream.jl:1698-1698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1699-1705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writepartial(s::LibuvStream, str::Union{String, SubString{String}};
                      cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    GC.@preserve str begin
        return Int(_unsafe_write_owned(s, pointer(str), UInt(sizeof(str)), cancel, str, true))
    end
end
```
-/
def writePartialOwnedString {World Stream A Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option A → Bool → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  let cancel ← precheck cancel
  let pointer ← pointer value
  let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
  JuliaLean.base.iostream.toInt (← writeOwned stream pointer size cancel (some value) true)

-- UNTRANSLATED
-- Source: base/stream.jl:1706-1709 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Owner-carrying counterpart of the generic `write(::IO, ::Array)` methods,
-- # again so a detached request keeps the array rooted (bits element types
-- # only; others error in the generic method anyway).
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1710-1718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::LibuvStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)
    if isbitstype(eltype(a))
        cancel = precheck_cancel_arg(cancel)
        GC.@preserve a begin
            return Int(_unsafe_write_owned(s, Ptr{UInt8}(pointer(a)), UInt(sizeof(a)), cancel, a, false))
        end
    end
    return invoke(write, Tuple{IO, AbstractArray}, s, a; cancel)
end
```
-/
def writeOwnedArray {World Stream A Token : Type}
    (isBits : A → M World Bool) (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option A → Bool → M World I)
    (fallback : Stream → A → CancelArg Token → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  if ← isBits value then
    let cancel ← precheck cancel
    let pointer ← pointer value
    let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
    return (← JuliaLean.base.iostream.toInt (← writeOwned stream pointer size cancel (some value) false))
  fallback stream value cancel

-- UNTRANSLATED
-- Source: base/stream.jl:1719-1719 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1720-1728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writepartial(s::LibuvStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)
    if isbitstype(eltype(a))
        cancel = precheck_cancel_arg(cancel)
        GC.@preserve a begin
            return Int(_unsafe_write_owned(s, Ptr{UInt8}(pointer(a)), UInt(sizeof(a)), cancel, a, true))
        end
    end
    return invoke(write, Tuple{IO, AbstractArray}, s, a; cancel)
end
```
-/
def writePartialOwnedArray {World Stream A Token : Type}
    (isBits : A → M World Bool) (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option A → Bool → M World I)
    (fallback : Stream → A → CancelArg Token → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  if ← isBits value then
    let cancel ← precheck cancel
    let pointer ← pointer value
    let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
    return (← JuliaLean.base.iostream.toInt (← writeOwned stream pointer size cancel (some value) true))
  fallback stream value cancel

-- UNTRANSLATED
-- Source: base/stream.jl:1729-1735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Raw-pointer writes have no discoverable owner: the caller's documented
-- # contract is pointer validity for the duration of the call - which an
-- # abandoning cancellation extends past the return, until the detached
-- # request's completion callback has run (see _detached_uvreq_roots). The
-- # owner-carrying entry points above (Vector{UInt8}, Array, String) do not
-- # have this hazard and are what the public `write` paths use.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1736-1739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_write(s::LibuvStream, p::Ptr{UInt8}, n::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    return _unsafe_write_owned(s, p, n, cancel, nothing, false)
end
```
-/
def unsafeWrite {World Stream Owner Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option Owner → Bool → M World I)
    (stream : Stream) (pointer : BytePointer) (count : U) (cancel : CancelArg Token) : M World I := do
  let cancel ← precheck cancel
  writeOwned stream pointer count cancel none false

-- UNTRANSLATED
-- Source: base/stream.jl:1740-1740 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1741-1772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _unsafe_write_owned(s::LibuvStream, p::Ptr{UInt8}, n::UInt, cancel::CancelTokenArg,
                             @nospecialize(owner), partial::Bool)
    while true
        # try to add to the send buffer
        iolock_begin()
        buf = s.sendbuf
        buf === nothing && break
        totb = bytesavailable(buf) + n
        if totb < buf.maxsize
            nb = unsafe_write(buf, p, n)
            iolock_end()
            return nb
        end
        bytesavailable(buf) == 0 && break
        # perform flush(s)
        arr = take!(buf)
        nb = uv_write(s, arr, cancel, true)
        if nb < length(arr)
            # a cancelled flush-write returns short: splice the unwritten
            # tail back (ahead of concurrent appends) so no buffered byte
            # is lost, then deliver - or, for the partial form, let the
            # next iteration's entry check deliver (level-triggered)
            _requeue_unwritten!(s, arr, nb)
            if !partial
                tok = resolve_cancel_token(cancel)
                tok === nothing || checkcancel(tok.source)
            end
        end
    end
    # perform the output to the kernel
    return _uv_write_owned(s, p, n, cancel, owner, partial)
end
```
-/
def unsafeWriteOwned {World Stream Buffer Condition Lock Vector Data Owner Token Source : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (beginIO endIO : M World Unit)
    (writeArray : Stream → Vector → CancelArg Token → Bool → M World I)
    (length : Vector → M World I) (requeue : Stream → Vector → I → M World Unit)
    (resolve : CancelArg Token → M World (Option Token)) (source : Token → M World Source)
    (checkcancel : Source → M World Unit)
    (writeKernel : Stream → BytePointer → U → CancelArg Token → Option Owner → Bool → M World I)
    (stream : Stream) (pointer : BytePointer) (count : U) (cancel : CancelArg Token)
    (owner : Option Owner) (partialWrite : Bool) : M World I := do
  let buffered ← JuliaLean.base.io.whileLoop (fun _ : Unit => do
    beginIO
    match (← access.get stream).sendbuf with
    | none => pure (.inl (none : Option I))
    | some buffer => do
      let available ← buffers.available buffer
      let available ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 available.val)
      let total := available + count
      if total.val < (← buffers.fields.get buffer).maxsize.val then
        let written ← buffers.unsafeWrite buffer pointer count
        endIO
        return .inl (some written)
      if (← buffers.available buffer).val = 0 then return .inl none
      let array ← buffers.take buffer
      let written ← writeArray stream array cancel true
      if written.val < (← length array).val then
        requeue stream array written
        if !partialWrite then
          match ← resolve cancel with
          | none => pure ()
          | some token => checkcancel (← source token)
      pure (.inr ())) ()
  match buffered with
  | some count => pure count
  | none => writeKernel stream pointer count cancel owner partialWrite

-- UNTRANSLATED
-- Source: base/stream.jl:1773-1777 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Splice the unwritten tail of a cancelled buffered-flush write back to the
-- # *front* of `s.sendbuf` - ahead of anything appended while the write was in
-- # flight, preserving stream order. `arr` was taken off the send buffer and
-- # only its first `nwritten` bytes reached the stream.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1778-1789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _requeue_unwritten!(s::LibuvStream, arr::Vector{UInt8}, nwritten::Int)
    nwritten < length(arr) || return nothing
    iolock_begin()
    buf = s.sendbuf
    if buf !== nothing
        appended = bytesavailable(buf) > 0 ? take!(buf) : nothing
        write(buf, @view arr[nwritten+1:end])
        appended === nothing || write(buf, appended)
    end
    iolock_end()
    return nothing
end
```
-/
def requeueUnwritten {World Stream Buffer Condition Lock Vector Data View : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (length : Vector → M World I)
    (beginIO endIO : M World Unit) (view : Vector → I → I → M World View)
    (writeView : Buffer → View → M World I) (writeArray : Buffer → Vector → M World I)
    (stream : Stream) (array : Vector) (written : I) : M World Unit := do
  if written.val ≥ (← length array).val then return ()
  beginIO
  match (← access.get stream).sendbuf with
  | none => pure ()
  | some buffer => do
    let appended ← if (← buffers.available buffer).val > 0 then do
      pure (some (← buffers.take buffer))
      else pure none
    let _ ← writeView buffer (← view array (written + i 1) (← length array))
    match appended with
    | none => pure ()
    | some appended => do let _ ← writeArray buffer appended; pure ()
  endIO

-- UNTRANSLATED
-- Source: base/stream.jl:1790-1794 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Cancellation contract of flush: a cancellation interrupts the wait and
-- # throws, but never silently discards data - buffered bytes that did not
-- # reach the stream are put back in the send buffer (a later flush retries
-- # them) and the partial state is left consistent.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1795-1824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function flush(s::LibuvStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    cancel = precheck_cancel_arg(cancel)
    iolock_begin()
    buf = s.sendbuf
    if buf !== nothing
        if bytesavailable(buf) > 0
            arr = take!(buf)
            nb = uv_write(s, arr, cancel, true)
            if nb < length(arr)
                # cancelled short: requeue the unwritten tail rather than
                # drop it - it stays buffered for a later flush - then
                # deliver the cancellation
                _requeue_unwritten!(s, arr, nb)
                tok = resolve_cancel_token(cancel)
                tok === nothing || checkcancel(tok.source)
            end
            return
        end
    end
    # zero write from a random pointer to flush current queue, ignoring any
    # errors from it: previously queued writes have already reported their
    # errors to their writers, and the peer closing the stream after a
    # completed exchange must not make flush throw
    try
        _uv_write_owned(s, Ptr{UInt8}(Base.eventloop()), UInt(0), cancel, nothing, false)
    catch ex
        ex isa IOError || rethrow()
    end
    return
end
```
-/
def flush {World Stream Buffer Condition Lock Vector Data Token Owner Source : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (precheck : CancelArg Token → M World (CancelArg Token))
    (beginIO : M World Unit) (writeArray : Stream → Vector → CancelArg Token → Bool → M World I)
    (length : Vector → M World I) (requeue : Stream → Vector → I → M World Unit)
    (resolve : CancelArg Token → M World (Option Token)) (source : Token → M World Source)
    (checkcancel : Source → M World Unit) (eventloop : M World Handle)
    (writeKernel : Stream → BytePointer → U → CancelArg Token → Option Owner → Bool → M World I)
    (isIOError : Error → Bool) (stream : Stream) (cancel : CancelArg Token) : M World Unit := do
  let cancel ← precheck cancel
  beginIO
  let buffered ← match (← access.get stream).sendbuf with
    | none => pure false
    | some buffer => do
      if (← buffers.available buffer).val > 0 then
        let array ← buffers.take buffer
        let written ← writeArray stream array cancel true
        if written.val < (← length array).val then
          requeue stream array written
          match ← resolve cancel with
          | none => pure ()
          | some token => checkcancel (← source token)
        pure true
      else pure false
  if buffered then return ()
  tryCatch (do
    let loop ← eventloop
    let _ ← writeKernel stream ⟨loop.address⟩ (u 0) cancel none false
    pure ()) (fun error => if isIOError error then pure () else throw error)

-- UNTRANSLATED
-- Source: base/stream.jl:1825-1825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1826-1832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function buffer_writes(s::LibuvStream, bufsize)
    sendbuf = PipeBuffer(bufsize)
    iolock_begin()
    s.sendbuf = sendbuf
    iolock_end()
    return s
end
```
-/
def bufferWrites {World Stream Buffer Condition Lock N : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (pipeBuffer : N → M World Buffer) (beginIO endIO : M World Unit)
    (stream : Stream) (size : N) : M World Stream := do
  let buffer ← pipeBuffer size
  beginIO
  access.set stream { (← access.get stream) with sendbuf := some buffer }
  endIO
  pure stream

-- UNTRANSLATED
-- Source: base/stream.jl:1833-1835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## low-level calls to libuv ##
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1836-1854 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::LibuvStream, b::UInt8)
    buf = s.sendbuf
    if buf !== nothing
        iolock_begin()
        if bytesavailable(buf) + 1 < buf.maxsize
            n = write(buf, b)
            iolock_end()
            return n
        end
        iolock_end()
    end
    # carry the Ref as the owner (rather than the generic ownerless
    # `write(s, ::Ref)` path): an abandoning cancellation may detach the
    # in-flight request, which must keep the byte's storage rooted
    r = Ref{UInt8}(b)
    GC.@preserve r begin
        return Int(_unsafe_write_owned(s, unsafe_convert(Ptr{UInt8}, r), UInt(1), DEFAULT_CANCEL, r, false))
    end
end
```
-/
def writeByte {World Stream Buffer Condition Lock Vector Data Ref Token : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (beginIO endIO : M World Unit)
    (writeByte : Buffer → Byte → M World I) (newRef : Byte → M World Ref)
    (pointer : Ref → M World BytePointer)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option Ref → Bool → M World I)
    (stream : Stream) (value : Byte) : M World I := do
  let buffer := (← access.get stream).sendbuf
  match buffer with
  | none => pure ()
  | some buffer => do
    beginIO
    if ((← buffers.available buffer) + i 1).val < (← buffers.fields.get buffer).maxsize.val then
      let count ← writeByte buffer value
      endIO
      return count
    endIO
  let reference ← newRef value
  JuliaLean.base.iostream.toInt (← writeOwned stream (← pointer reference) (u 1) .default (some reference) false)

-- Source: base/stream.jl:1855-1855 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/stream.jl:1908-1908 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


/--
Julia source: base/stream.jl:1909-1913 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_shutdowncb_task(req::Ptr{Cvoid}, status::Cint)
    t = _claim_uvreq_waiter(req)
    t === nothing || schedule(t, status)
    nothing
end
```
-/
def uvShutdownCallback {World Task : Type}
    (claim : Handle → M World (Option Task)) (schedule : Task → CInt → M World Unit)
    (request : Handle) (status : CInt) : M World Unit := do
  match ← claim request with
  | none => pure ()
  | some task => schedule task status

-- UNTRANSLATED
-- Source: base/stream.jl:1914-1915 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1916-1916 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_fd(x::IOStream) = RawFD(fd(x))
```
-/
def fdIOStream {World Stream FD : Type} (fd : Stream → M World FD)
    (rawFD : FD → M World FD) (stream : Stream) : M World FD := do rawFD (← fd stream)

/--
Julia source: base/stream.jl:1917-1917 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_fd(x::Union{OS_HANDLE, RawFD}) = x
```
-/
def fdHandle {FD : Type} (descriptor : FD) : FD := descriptor

-- UNTRANSLATED
-- Source: base/stream.jl:1918-1918 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1919-1926 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _fd(x::Union{LibuvStream, LibuvServer})
    fd = Ref{OS_HANDLE}(INVALID_OS_HANDLE)
    if x.status != StatusUninit && x.status != StatusClosed && x.handle != C_NULL
        ccall(:uv_fileno, Int32, (Ptr{Cvoid}, Ptr{OS_HANDLE}), x.handle, fd)
        # handle errors by returning INVALID_OS_HANDLE
    end
    return fd[]
end
```
-/
def fdLibuv {World Ref Condition FD FDRef : Type} (metadata : Metadata World Ref Condition)
    (invalid : FD) (newRef : FD → M World FDRef) (get : FDRef → M World FD)
    (fileno : Handle → FDRef → M World CInt) (reference : Ref) : M World FD := do
  let fd ← newRef invalid
  if (← metadata.status reference).val != 0 then
    if (← metadata.status reference).val != 6 then
      if (← metadata.handle reference).address.val != 0 then
        let _ ← fileno (← metadata.handle reference) fd
  get fd

-- UNTRANSLATED
-- Source: base/stream.jl:1927-1937 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- struct RedirectStdStream <: Function
--     unix_fd::Int
--     writable::Bool
-- end
-- for (f, writable, unix_fd) in
--         ((:redirect_stdin, false, 0),
--          (:redirect_stdout, true, 1),
--          (:redirect_stderr, true, 2))
--     @eval const ($f) = RedirectStdStream($unix_fd, $writable)
-- end
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1938-1948 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _redirect_io_libc(stream, unix_fd::Int)
    posix_fd = _fd(stream)
    @static if Sys.iswindows()
        if 0 <= unix_fd <= 2
            ccall(:SetStdHandle, stdcall, Int32, (Int32, OS_HANDLE),
                -10 - unix_fd, Libc._get_osfhandle(posix_fd))
        end
    end
    GC.@preserve stream dup(posix_fd, RawFD(unix_fd))
    nothing
end
```
-/
def redirectLibc {World Stream FD : Type} (fd : Stream → M World FD)
    (getOSHandle : FD → M World Handle) (setStdHandle : CInt → Handle → M World CInt)
    (rawFD : I → M World FD) (dup : FD → FD → M World FD)
    (windows : Bool) (stream : Stream) (unixFD : I) : M World Unit := do
  let descriptor ← fd stream
  if windows then
    if 0 ≤ unixFD.val && unixFD.val ≤ 2 then
      let _ ← setStdHandle (JInt.rem .i32 (i (-10) - unixFD)) (← getOSHandle descriptor)
  let _ ← dup descriptor (← rawFD unixFD)
  pure ()

/--
Julia source: base/stream.jl:1949-1956 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _redirect_io_cglobal(handle::Union{LibuvStream, IOStream, Nothing}, unix_fd::Int)
    c_sym = unix_fd == 0 ? cglobal(:jl_uv_stdin, Ptr{Cvoid}) :
            unix_fd == 1 ? cglobal(:jl_uv_stdout, Ptr{Cvoid}) :
            unix_fd == 2 ? cglobal(:jl_uv_stderr, Ptr{Cvoid}) :
            C_NULL
    c_sym == C_NULL || unsafe_store!(c_sym, handle === nothing ? Ptr{Cvoid}(unix_fd) : handle.handle)
    nothing
end
```
-/
def redirectCGlobal {World Stream : Type}
    (cglobal : I → M World (JuliaLean.base.pointer.Ptr Handle))
    (handle : Stream → M World Handle)
    (store : JuliaLean.base.pointer.Ptr Handle → Handle → M World Unit)
    (stream : Option Stream) (unixFD : I) : M World Unit := do
  let symbol ← if unixFD.val = 0 then cglobal (i 0)
    else if unixFD.val = 1 then cglobal (i 1)
    else if unixFD.val = 2 then cglobal (i 2)
    else pure ⟨u 0⟩
  if symbol.address.val != 0 then
    let value ← match stream with
      | none => pure (⟨JInt.rem .u64 unixFD⟩ : Handle)
      | some stream => handle stream
    store symbol value

/--
Julia source: base/stream.jl:1957-1962 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _redirect_io_global(io, unix_fd::Int)
    unix_fd == 0 && (global stdin = io)
    unix_fd == 1 && (global stdout = io)
    unix_fd == 2 && (global stderr = io)
    nothing
end
```
-/
def redirectGlobal {World Stream : Type} (setStdin setStdout setStderr : Stream → M World Unit)
    (stream : Stream) (unixFD : I) : M World Unit := do
  if unixFD.val = 0 then setStdin stream
  if unixFD.val = 1 then setStdout stream
  if unixFD.val = 2 then setStderr stream

/--
Julia source: base/stream.jl:1963-1968 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (f::RedirectStdStream)(handle::Union{LibuvStream, IOStream})
    _redirect_io_libc(handle, f.unix_fd)
    _redirect_io_cglobal(handle, f.unix_fd)
    _redirect_io_global(handle, f.unix_fd)
    return handle
end
```
-/
def redirectHandle {World Stream : Type}
    (redirectLibc : Stream → I → M World Unit)
    (redirectCGlobal : Option Stream → I → M World Unit)
    (redirectGlobal : Stream → I → M World Unit)
    (redirect : RedirectStdStream) (stream : Stream) : M World Stream := do
  redirectLibc stream redirect.unixFD
  redirectCGlobal (some stream) redirect.unixFD
  redirectGlobal stream redirect.unixFD
  pure stream

/--
Julia source: base/stream.jl:1969-1977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (f::RedirectStdStream)(::DevNull)
    nulldev = @static Sys.iswindows() ? "NUL" : "/dev/null"
    handle = open(nulldev, write=f.writable)
    _redirect_io_libc(handle, f.unix_fd)
    close(handle) # handle has been dup'ed in _redirect_io_libc
    _redirect_io_cglobal(nothing, f.unix_fd)
    _redirect_io_global(devnull, f.unix_fd)
    return devnull
end
```
-/
def redirectDevNull {World Stream : Type} (openFile : String → Bool → M World Stream)
    (redirectLibc : Stream → I → M World Unit) (close : Stream → M World Unit)
    (redirectCGlobal : Option Stream → I → M World Unit)
    (redirectGlobal : JuliaLean.base.coreio.DevNull → I → M World Unit)
    (windows : Bool) (redirect : RedirectStdStream) (_null : JuliaLean.base.coreio.DevNull) :
    M World JuliaLean.base.coreio.DevNull := do
  let stream ← openFile (if windows then "NUL" else "/dev/null") redirect.writable
  redirectLibc stream redirect.unixFD
  close stream
  redirectCGlobal none redirect.unixFD
  redirectGlobal JuliaLean.base.coreio.devnull redirect.unixFD
  pure JuliaLean.base.coreio.devnull

/--
Julia source: base/stream.jl:1978-1983 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (f::RedirectStdStream)(io::AbstractPipe)
    io2 = (f.writable ? pipe_writer : pipe_reader)(io)
    f(io2)
    _redirect_io_global(io, f.unix_fd)
    return io
end
```
-/
def redirectAbstractPipe {World PipeRef Stream : Type}
    (reader writer : PipeRef → M World Stream) (apply : RedirectStdStream → Stream → M World Stream)
    (redirectGlobal : PipeRef → I → M World Unit) (redirect : RedirectStdStream) (pipe : PipeRef) : M World PipeRef := do
  let stream ← if redirect.writable then writer pipe else reader pipe
  let _ ← apply redirect stream
  redirectGlobal pipe redirect.unixFD
  pure pipe

/--
Julia source: base/stream.jl:1984-1991 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (f::RedirectStdStream)(p::Pipe)
    if p.in.status == StatusInit && p.out.status == StatusInit
        link_pipe!(p)
    end
    io2 = getfield(p, f.writable ? :in : :out)
    f(io2)
    return p
end
```
-/
def redirectPipe {World Ref Endpoint Condition : Type} (access : Access World Ref (Pipe Endpoint))
    (metadata : Metadata World Endpoint Condition) (link : Ref → M World Ref)
    (apply : RedirectStdStream → Endpoint → M World Endpoint)
    (redirect : RedirectStdStream) (pipe : Ref) : M World Ref := do
  if (← metadata.status (← access.get pipe).input).val = 1 then
    if (← metadata.status (← access.get pipe).output).val = 1 then
      let _ ← link pipe
  let fields ← access.get pipe
  let stream := if redirect.writable then fields.input else fields.output
  let _ ← apply redirect stream
  pure pipe

/--
Julia source: base/stream.jl:1992-1992 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(f::RedirectStdStream)() = f(Pipe())
```
-/
def redirectNewPipe {World PipeRef : Type} (newPipe : M World PipeRef)
    (apply : RedirectStdStream → PipeRef → M World PipeRef) (redirect : RedirectStdStream) : M World PipeRef := do
  apply redirect (← newPipe)

-- UNTRANSLATED
-- Source: base/stream.jl:1993-1994 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Deprecate these in v2 (RedirectStdStream support)
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:1995-1995 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(p::Pipe) = (p.out, 1)
```
-/
def pipeIterate {World Ref Endpoint : Type} (access : Access World Ref (Pipe Endpoint))
    (pipe : Ref) : M World (Endpoint × I) := do pure ((← access.get pipe).output, i 1)

/--
Julia source: base/stream.jl:1996-1996 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(p::Pipe, i::Int) = i == 1 ? (p.in, 2) : nothing
```
-/
def pipeIterateNext {World Ref Endpoint : Type} (access : Access World Ref (Pipe Endpoint))
    (pipe : Ref) (state : I) : M World (Option (Endpoint × I)) := do
  if state.val = 1 then pure (some ((← access.get pipe).input, i 2)) else pure none

/--
Julia source: base/stream.jl:1997-1997 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(p::Pipe, key::Int) = key == 1 ? p.out : key == 2 ? p.in : throw(KeyError(key))
```
-/
def pipeGetindex {World Ref Endpoint : Type} (access : Access World Ref (Pipe Endpoint))
    (pipe : Ref) (key : I) : M World Endpoint := do
  if key.val = 1 then pure (← access.get pipe).output
  else if key.val = 2 then pure (← access.get pipe).input
  else throw (.foreignError "KeyError" "pipe index")

-- UNTRANSLATED
-- Source: base/stream.jl:1998-2051 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     redirect_stdout([stream]) -> stream
-- 
-- Create a pipe to which all C and Julia level [`stdout`](@ref) output
-- will be redirected. Return a stream representing the pipe ends.
-- Data written to [`stdout`](@ref) may now be read from the `rd` end of
-- the pipe.
-- 
-- !!! note
--     `stream` must be a compatible objects, such as an `IOStream`, `TTY`,
--     [`Pipe`](@ref), socket, or `devnull`.
-- 
-- See also [`redirect_stdio`](@ref).
-- """
-- redirect_stdout
-- 
-- """
--     redirect_stderr([stream]) -> stream
-- 
-- Like [`redirect_stdout`](@ref), but for [`stderr`](@ref).
-- 
-- !!! note
--     `stream` must be a compatible objects, such as an `IOStream`, `TTY`,
--     [`Pipe`](@ref), socket, or `devnull`.
-- 
-- See also [`redirect_stdio`](@ref).
-- """
-- redirect_stderr
-- 
-- """
--     redirect_stdin([stream]) -> stream
-- 
-- Like [`redirect_stdout`](@ref), but for [`stdin`](@ref).
-- Note that the direction of the stream is reversed.
-- 
-- !!! note
--     `stream` must be a compatible objects, such as an `IOStream`, `TTY`,
--     [`Pipe`](@ref), socket, or `devnull`.
-- 
-- See also [`redirect_stdio`](@ref).
-- """
-- redirect_stdin
-- 
-- """
--     redirect_stdio(;stdin=stdin, stderr=stderr, stdout=stdout)
-- 
-- Redirect a subset of the streams `stdin`, `stderr`, `stdout`.
-- Each argument must be an `IOStream`, `TTY`, [`Pipe`](@ref), socket, or
-- `devnull`.
-- 
-- !!! compat "Julia 1.7"
--     `redirect_stdio` requires Julia 1.7 or later.
-- """
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2052-2056 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function redirect_stdio(;stdin=nothing, stderr=nothing, stdout=nothing)
    stdin  === nothing || redirect_stdin(stdin)
    stderr === nothing || redirect_stderr(stderr)
    stdout === nothing || redirect_stdout(stdout)
end
```
-/
def redirectStdio {World Stream : Type} (input error output : Stream → M World Unit)
    (stdin stderr stdout : Option Stream) : M World Unit := do
  match stdin with | none => pure () | some stream => input stream
  match stderr with | none => pure () | some stream => error stream
  match stdout with | none => pure () | some stream => output stream

-- UNTRANSLATED
-- Source: base/stream.jl:2057-2109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     redirect_stdio(f; stdin=nothing, stderr=nothing, stdout=nothing)
-- 
-- Redirect a subset of the streams `stdin`, `stderr`, `stdout`,
-- call `f()` and restore each stream.
-- 
-- Possible values for each stream are:
-- * `nothing` indicating the stream should not be redirected.
-- * `path::AbstractString` redirecting the stream to the file at `path`.
-- * `io` an `IOStream`, `TTY`, [`Pipe`](@ref), socket, or `devnull`.
-- 
-- # Examples
-- ```julia-repl
-- julia> redirect_stdio(stdout="stdout.txt", stderr="stderr.txt") do
--            print("hello stdout")
--            print(stderr, "hello stderr")
--        end
-- 
-- julia> read("stdout.txt", String)
-- "hello stdout"
-- 
-- julia> read("stderr.txt", String)
-- "hello stderr"
-- ```
-- 
-- # Edge cases
-- 
-- It is possible to pass the same argument to `stdout` and `stderr`:
-- ```julia-repl
-- julia> redirect_stdio(stdout="log.txt", stderr="log.txt", stdin=devnull) do
--     ...
-- end
-- ```
-- 
-- However it is not supported to pass two distinct descriptors of the same file.
-- ```julia-repl
-- julia> io1 = open("same/path", "w")
-- 
-- julia> io2 = open("same/path", "w")
-- 
-- julia> redirect_stdio(f, stdout=io1, stderr=io2) # not supported
-- ```
-- Also the `stdin` argument may not be the same descriptor as `stdout` or `stderr`.
-- ```julia-repl
-- julia> io = open(...)
-- 
-- julia> redirect_stdio(f, stdout=io, stdin=io) # not supported
-- ```
-- 
-- !!! compat "Julia 1.7"
--     `redirect_stdio` requires Julia 1.7 or later.
-- """
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2110-2154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function redirect_stdio(f; stdin=nothing, stderr=nothing, stdout=nothing)

    function resolve(new::Nothing, oldstream, mode)
        (new=nothing, close=false, old=nothing)
    end
    function resolve(path::AbstractString, oldstream,mode)
        (new=open(path, mode), close=true, old=oldstream)
    end
    function resolve(new, oldstream, mode)
        (new=new, close=false, old=oldstream)
    end

    same_path(x, y) = false
    function same_path(x::AbstractString, y::AbstractString)
        # if x = y = "does_not_yet_exist.txt" then samefile will return false
        (abspath(x) == abspath(y)) || samefile(x,y)
    end
    if same_path(stderr, stdin)
        throw(ArgumentError("stdin and stderr cannot be the same path"))
    end
    if same_path(stdout, stdin)
        throw(ArgumentError("stdin and stdout cannot be the same path"))
    end

    new_in , close_in , old_in  = resolve(stdin , Base.stdin , "r")
    new_out, close_out, old_out = resolve(stdout, Base.stdout, "w")
    if same_path(stderr, stdout)
        # make sure that in case stderr = stdout = "same/path"
        # only a single io is used instead of opening the same file twice
        new_err, close_err, old_err = new_out, false, Base.stderr
    else
        new_err, close_err, old_err = resolve(stderr, Base.stderr, "w")
    end

    redirect_stdio(; stderr=new_err, stdin=new_in, stdout=new_out)

    try
        return f()
    finally
        redirect_stdio(;stderr=old_err, stdin=old_in, stdout=old_out)
        close_err && close(new_err)
        close_in  && close(new_in )
        close_out && close(new_out)
    end
end
```
-/
def redirectStdioWith {World Path Stream Absolute A : Type}
    (abspath : Path → M World Absolute) (equal : Absolute → Absolute → M World Bool)
    (samefile : Path → Path → M World Bool) (openFile : Path → String → M World Stream)
    (getStdin getStdout getStderr : M World Stream)
    (redirect : Option Stream → Option Stream → Option Stream → M World Unit)
    (close : Stream → M World Unit) (action : M World A)
    (stdin stderr stdout : RedirectArg Path Stream) : M World A := do
  let samePath := fun left right => do
    match left, right with
    | .path left, .path right => redirectSamePath abspath equal samefile left right
    | left, right => pure (redirectSamePathAny left right)
  if ← samePath stderr stdin then
    throw (.jl (.argumentError "stdin and stderr cannot be the same path"))
  if ← samePath stdout stdin then
    throw (.jl (.argumentError "stdin and stdout cannot be the same path"))
  let resolve := fun value old mode => do
    match value with
    | .unchanged => pure (redirectResolveNothing old mode)
    | .stream value => pure (redirectResolveStream value old mode)
    | .path path => redirectResolvePath openFile path old mode
  let input ← resolve stdin (← getStdin) "r"
  let output ← resolve stdout (← getStdout) "w"
  let error ← if ← samePath stderr stdout then do
    let old ← getStderr
    pure (Resolution.borrowed output.current old)
    else resolve stderr (← getStderr) "w"
  redirect input.current error.current output.current
  JuliaLean.base.io.finallyDo action (do
    redirect input.previous error.previous output.previous
    closeResolution close error
    closeResolution close input
    closeResolution close output)

-- UNTRANSLATED
-- Source: base/stream.jl:2155-2155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2156-2167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (f::RedirectStdStream)(thunk::Function, stream)
    stdold = f.unix_fd == 0 ? stdin :
             f.unix_fd == 1 ? stdout :
             f.unix_fd == 2 ? stderr :
             throw(ArgumentError("Not implemented to get old handle of fd except for stdio"))
    f(stream)
    try
        return thunk()
    finally
        f(stdold)
    end
end
```
-/
def redirectThunk {World Stream Other A : Type}
    (stdin stdout stderr : M World Stream)
    (apply : RedirectStdStream → Other → M World Other)
    (restore : RedirectStdStream → Stream → M World Stream)
    (redirect : RedirectStdStream) (action : M World A) (stream : Other) : M World A := do
  let previous ← if redirect.unixFD.val = 0 then stdin
    else if redirect.unixFD.val = 1 then stdout
    else if redirect.unixFD.val = 2 then stderr
    else throw (.jl (.argumentError "Not implemented to get old handle of fd except for stdio"))
  let _ ← apply redirect stream
  JuliaLean.base.io.finallyDo action (restore redirect previous)

-- UNTRANSLATED
-- Source: base/stream.jl:2168-2193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
--     redirect_stdout(f::Function, stream)
-- 
-- Run the function `f` while redirecting [`stdout`](@ref) to `stream`.
-- Upon completion, [`stdout`](@ref) is restored to its prior setting.
-- """
-- redirect_stdout(f::Function, stream)
-- 
-- """
--     redirect_stderr(f::Function, stream)
-- 
-- Run the function `f` while redirecting [`stderr`](@ref) to `stream`.
-- Upon completion, [`stderr`](@ref) is restored to its prior setting.
-- """
-- redirect_stderr(f::Function, stream)
-- 
-- """
--     redirect_stdin(f::Function, stream)
-- 
-- Run the function `f` while redirecting [`stdin`](@ref) to `stream`.
-- Upon completion, [`stdin`](@ref) is restored to its prior setting.
-- """
-- redirect_stdin(f::Function, stream)
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2194-2194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mark(x::LibuvStream)     = mark(x.buffer)
```
-/
def markStream {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (mark : Buffer → M World I) (stream : Stream) : M World I := do
  mark (← access.get stream).buffer

/--
Julia source: base/stream.jl:2195-2195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unmark(x::LibuvStream)   = unmark(x.buffer)
```
-/
def unmarkStream {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (unmark : Buffer → M World Bool) (stream : Stream) : M World Bool := do
  unmark (← access.get stream).buffer

/--
Julia source: base/stream.jl:2196-2196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reset(x::LibuvStream)    = reset(x.buffer)
```
-/
def resetStream {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (reset : Buffer → M World I) (stream : Stream) : M World I := do
  reset (← access.get stream).buffer

/--
Julia source: base/stream.jl:2197-2197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ismarked(x::LibuvStream) = ismarked(x.buffer)
```
-/
def ismarkedStream {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (ismarked : Buffer → M World Bool) (stream : Stream) : M World Bool := do
  ismarked (← access.get stream).buffer

-- UNTRANSLATED
-- Source: base/stream.jl:2198-2198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2199-2205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek(s::LibuvStream, ::Type{T}) where T
    mark(s)
    try read(s, T)
    finally
        reset(s)
    end
end
```
-/
def peek {World Stream T Mark Reset : Type} (mark : Stream → M World Mark)
    (read : Stream → M World T) (reset : Stream → M World Reset) (stream : Stream) : M World T := do
  let _ ← mark stream
  JuliaLean.base.io.finallyDo (read stream) (reset stream)

-- UNTRANSLATED
-- Source: base/stream.jl:2206-2215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # BufferStream's are non-OS streams, backed by a regular IOBuffer
-- mutable struct BufferStream <: LibuvStream
--     buffer::IOBuffer
--     cond::Threads.Condition
--     readerror::Any
--     buffer_writes::Bool
--     lock::ReentrantLock # advisory lock
--     status::Int
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2216-2216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    BufferStream() = new(PipeBuffer(), Threads.Condition(), nothing, false, ReentrantLock(), StatusActive)
```
-/
def bufferStream {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (pipeBuffer : M World Buffer) (newCondition : M World Condition) (newLock : M World Lock) : M World Stream := do
  let buffer ← pipeBuffer
  let condition ← newCondition
  let mutex ← newLock
  access.new ⟨buffer, condition, none, false, mutex, statusActive⟩

-- UNTRANSLATED
-- Source: base/stream.jl:2217-2218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2219-2219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isopen(s::BufferStream) = s.status != StatusClosed
```
-/
def bufferIsopen {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock)) (stream : Stream) : M World Bool := do
  pure ((← access.get stream).status.val != 6)

-- UNTRANSLATED
-- Source: base/stream.jl:2220-2224 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # BufferStream <: LibuvStream, so every keyword-accepting LibuvStream
-- # method a `cancel=` call would select must be re-specialized here: keyword
-- # calls dispatch only among keyword-accepting methods, and the LibuvStream
-- # ones touch fields (handle, sendbuf) a BufferStream does not have.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2225-2229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function closewrite(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    # closing is in-memory and immediate: entry gate only
    precheck_cancel_arg(cancel)
    close(s)
end
```
-/
def bufferClosewrite {World Stream Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token)) (close : Stream → M World Unit)
    (stream : Stream) (cancel : CancelArg Token) : M World Unit := do
  let _ ← precheck cancel
  close stream

-- UNTRANSLATED
-- Source: base/stream.jl:2230-2230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2231-2237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function close(s::BufferStream)
    lock(s.cond) do
        s.status = StatusClosed
        notify(s.cond) # aka flush
        nothing
    end
end
```
-/
def bufferClose {World Stream Buffer Condition Lock Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (ops : ConditionOps World Condition Token) (stream : Stream) : M World Unit := do
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    access.set stream { (← access.get stream) with status := statusClosed }
    ops.notify (← access.get stream).condition)

/--
Julia source: base/stream.jl:2238-2238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
uvfinalize(s::BufferStream) = nothing
```
-/
def bufferFinalize {World Stream : Type} (_stream : Stream) : M World Unit := pure ()

/--
Julia source: base/stream.jl:2239-2239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setup_stdio(stream::BufferStream, child_readable::Bool) = invoke(setup_stdio, Tuple{IO, Bool}, stream, child_readable)
```
-/
def bufferSetupStdio {World Stream Result : Type}
    (genericSetup : Stream → Bool → M World Result) (stream : Stream) (childReadable : Bool) : M World Result :=
  genericSetup stream childReadable

-- UNTRANSLATED
-- Source: base/stream.jl:2240-2240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2241-2248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(s::BufferStream, ::Type{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    nread = lock(s.cond) do
        wait_readnb(s, 1, tok)
        read(s.buffer, UInt8)
    end
    return nread
end
```
-/
def bufferReadByte {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitRead : Stream → I → Option Token → M World Unit)
    (stream : Stream) (cancel : CancelArg Token) : M World Byte := do
  let token ← resolve (← precheck cancel)
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    waitRead stream (i 1) token
    buffers.readByte (← access.get stream).buffer)

/--
Julia source: base/stream.jl:2249-2256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_read(s::BufferStream, a::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    lock(s.cond) do
        wait_readnb(s, Int(nb), tok)
        unsafe_read(s.buffer, a, nb)
        nothing
    end
end
```
-/
def bufferUnsafeRead {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitRead : Stream → I → Option Token → M World Unit)
    (stream : Stream) (pointer : BytePointer) (count : U) (cancel : CancelArg Token) : M World Unit := do
  let token ← resolve (← precheck cancel)
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    waitRead stream (← JuliaLean.base.iostream.toInt count) token
    buffers.unsafeRead (← access.get stream).buffer pointer count)

/--
Julia source: base/stream.jl:2257-2257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bytesavailable(s::BufferStream) = bytesavailable(s.buffer)
```
-/
def bufferBytesavailable {World Stream Buffer Condition Lock Vector Data : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (stream : Stream) : M World I := do
  buffers.available (← access.get stream).buffer

-- UNTRANSLATED
-- Source: base/stream.jl:2258-2258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2259-2259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isreadable(s::BufferStream) = (isopen(s) || bytesavailable(s) > 0) && s.buffer.readable
```
-/
def bufferIsreadable {World Stream Buffer Condition Lock Vector Data : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (stream : Stream) : M World Bool := do
  let ready ← if ← bufferIsopen access stream then pure true
    else pure ((← bufferBytesavailable access buffers stream).val > 0)
  if ready then pure (← buffers.fields.get (← access.get stream).buffer).readable else pure false

/--
Julia source: base/stream.jl:2260-2260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iswritable(s::BufferStream) = isopen(s) && s.buffer.writable
```
-/
def bufferIswritable {World Stream Buffer Condition Lock Vector Data : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (stream : Stream) : M World Bool := do
  if ← bufferIsopen access stream then pure (← buffers.fields.get (← access.get stream).buffer).writable
  else pure false

-- UNTRANSLATED
-- Source: base/stream.jl:2261-2261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2262-2275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_readnb(s::BufferStream, nb::Int, tok::MaybeToken=default_cancel_token())
    lock(s.cond)
    locked = true
    try
        while isopen(s) && bytesavailable(s.buffer) < nb
            locked = false
            wait(s.cond, tok)
            locked = true
        end
    finally
        locked && unlock(s.cond)
    end
    nothing
end
```
-/
def bufferWaitRead {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (stream : Stream) (count : I) (token : Option Token) : M World Unit := do
  ops.lock (← access.get stream).condition
  let (locked, result) ← conditionWaitLoop (do
    if ← bufferIsopen access stream then
      pure ((← buffers.available (← access.get stream).buffer).val < count.val)
    else pure false) (do ops.wait (← access.get stream).condition token)
  JuliaLean.base.io.finallyDo (rethrowResult result) (do
    if locked then ops.unlock (← access.get stream).condition)

-- UNTRANSLATED
-- Source: base/stream.jl:2276-2276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2277-2286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readavailable(this::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    bytes = lock(this.cond) do
        wait_readnb(this, 1, tok)
        buf = this.buffer
        @assert buf.seekable == false "buffer should not be seekable"
        take!(buf)
    end
    return bytes
end
```
-/
def bufferReadavailable {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitRead : Stream → I → Option Token → M World Unit)
    (stream : Stream) (cancel : CancelArg Token) : M World Vector := do
  let token ← resolve (← precheck cancel)
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    waitRead stream (i 1) token
    let buffer := (← access.get stream).buffer
    if (← buffers.fields.get buffer).seekable then
      throw (.foreignError "AssertionError" "buffer should not be seekable")
    buffers.take buffer)

-- UNTRANSLATED
-- Source: base/stream.jl:2287-2287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2288-2295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(stream::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    bytes = lock(stream.cond) do
        wait_close(stream, tok)
        take!(stream.buffer)
    end
    return bytes
end
```
-/
def bufferReadAll {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitClose : Stream → Option Token → M World Unit)
    (stream : Stream) (cancel : CancelArg Token) : M World Vector := do
  let token ← resolve (← precheck cancel)
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    waitClose stream token
    buffers.take (← access.get stream).buffer)

-- UNTRANSLATED
-- Source: base/stream.jl:2296-2296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2297-2335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readbytes!(s::BufferStream, a::Vector{UInt8}, nb::Int; cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    sbuf = s.buffer
    @assert sbuf.seekable == false "buffer should not be seekable"
    @assert sbuf.maxsize >= nb "insufficient buffer size"

    function wait_locked(s, buf, nb, tok)
        while bytesavailable(buf) < nb
            s.readerror === nothing || throw(s.readerror)
            isopen(s) || break
            s.status != StatusEOF || break
            wait_readnb(s, nb, tok)
        end
    end

    bytes = lock(s.cond) do
        if nb <= SZ_UNBUFFERED_IO # Under this limit we are OK with copying the array from the stream's buffer
            wait_locked(s, sbuf, nb, tok)
        end
        if bytesavailable(sbuf) >= nb
            nread = readbytes!(sbuf, a, nb)
        else
            initsize = length(a)
            newbuf = _truncated_pipebuffer(a; maxsize=nb)
            nread = try
                s.buffer = newbuf
                write(newbuf, sbuf)
                wait_locked(s, newbuf, nb, tok)
                bytesavailable(newbuf)
            finally
                s.buffer = sbuf
            end
            _take!(a, _unsafe_take!(newbuf))
            length(a) >= initsize || resize!(a, initsize)
        end
        return nread
    end
    return bytes
end
```
-/
def bufferReadbytes {World Stream Buffer Condition Lock Vector Data Token Taken : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitRead : Stream → I → Option Token → M World Unit)
    (length : Vector → M World I) (truncatePipe : Vector → I → M World Buffer)
    (writeBuffer : Buffer → Buffer → M World I) (unsafeTake : Buffer → M World Taken)
    (takeInto : Vector → Taken → M World Unit) (resize : Vector → I → M World Unit)
    (stream : Stream) (array : Vector) (count : I) (cancel : CancelArg Token) : M World I := do
  let token ← resolve (← precheck cancel)
  let buffer := (← access.get stream).buffer
  if (← buffers.fields.get buffer).seekable then
    throw (.foreignError "AssertionError" "buffer should not be seekable")
  if (← buffers.fields.get buffer).maxsize.val < count.val then
    throw (.foreignError "AssertionError" "insufficient buffer size")
  let waitLocked := fun target => bufferWaitReadLocked access buffers (bufferIsopen access) waitRead stream target count token
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    if count.val ≤ JuliaLean.base.io.szUnbufferedIO.val then waitLocked buffer
    if (← buffers.available buffer).val ≥ count.val then buffers.readbytes buffer array count
    else
      let initialSize ← length array
      let newBuffer ← truncatePipe array count
      let readCount ← JuliaLean.base.io.finallyDo (do
        access.set stream { (← access.get stream) with buffer := newBuffer }
        let _ ← writeBuffer newBuffer buffer
        waitLocked newBuffer
        buffers.available newBuffer) (do
          access.set stream { (← access.get stream) with buffer })
      takeInto array (← unsafeTake newBuffer)
      if (← length array).val < initialSize.val then resize array initialSize
      pure readCount)

-- UNTRANSLATED
-- Source: base/stream.jl:2336-2336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2337-2337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, s::BufferStream) = print(io, "BufferStream(bytes waiting=", bytesavailable(s.buffer), ", isopen=", isopen(s), ")")
```
-/
def bufferShow {World Stream Buffer Condition Lock Out : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (available : Buffer → M World I)
    (print : Out → List (ShowArg Unit Unit) → M World Unit) (out : Out) (stream : Stream) : M World Unit := do
  let count ← available (← access.get stream).buffer
  let opened ← bufferIsopen access stream
  print out [.text "BufferStream(bytes waiting=", .count count, .text ", isopen=", .boolean opened, .text ")"]

-- UNTRANSLATED
-- Source: base/stream.jl:2338-2338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2339-2356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function readuntil(s::BufferStream, c::UInt8; keep::Bool=false, cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    lock(s.cond)
    locked = true
    bytes = try
        while isopen(s) && !occursin(c, s.buffer)
            # a cancelled wait unwinds with the buffer intact (nothing has
            # been consumed until the delimiter is present)
            locked = false
            wait(s.cond, tok)
            locked = true
        end
        readuntil(s.buffer, c, keep=keep)
    finally
        locked && unlock(s.cond)
    end
    return bytes
end
```
-/
def bufferReaduntil {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (stream : Stream) (delim : Byte) (keep : Bool) (cancel : CancelArg Token) : M World Vector := do
  let token ← resolve (← precheck cancel)
  ops.lock (← access.get stream).condition
  let (locked, result) ← conditionWaitLoop (do
    if ← bufferIsopen access stream then pure (!(← buffers.occursin delim (← access.get stream).buffer))
    else pure false) (do ops.wait (← access.get stream).condition token)
  JuliaLean.base.io.finallyDo (do
    rethrowResult result
    buffers.readuntil (← access.get stream).buffer delim keep) (do
      if locked then ops.unlock (← access.get stream).condition)

-- UNTRANSLATED
-- Source: base/stream.jl:2357-2357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2358-2371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function wait_close(s::BufferStream, tok::MaybeToken=default_cancel_token())
    lock(s.cond)
    locked = true
    try
        while isopen(s)
            locked = false
            wait(s.cond, tok)
            locked = true
        end
    finally
        locked && unlock(s.cond)
    end
    nothing
end
```
-/
def bufferWaitClose {World Stream Buffer Condition Lock Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (ops : ConditionOps World Condition Token) (stream : Stream) (token : Option Token) : M World Unit := do
  ops.lock (← access.get stream).condition
  let (locked, result) ← conditionWaitLoop (bufferIsopen access stream)
    (do ops.wait (← access.get stream).condition token)
  JuliaLean.base.io.finallyDo (rethrowResult result) (do
    if locked then ops.unlock (← access.get stream).condition)

-- UNTRANSLATED
-- Source: base/stream.jl:2372-2372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2373-2373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
start_reading(s::BufferStream) = Int32(0)
```
-/
def bufferStartReading {World Stream : Type} (_stream : Stream) : M World CInt := pure (cint 0)

/--
Julia source: base/stream.jl:2374-2374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stop_reading(s::BufferStream) = nothing
```
-/
def bufferStopReading {World Stream : Type} (_stream : Stream) : M World Unit := pure ()

-- UNTRANSLATED
-- Source: base/stream.jl:2375-2375 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2376-2376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(s::BufferStream, b::UInt8) = write(s, Ref{UInt8}(b))
```
-/
def bufferWriteByte {World Stream Ref : Type} (newRef : Byte → M World Ref)
    (write : Stream → Ref → M World I) (stream : Stream) (value : Byte) : M World I := do
  write stream (← newRef value)

-- UNTRANSLATED
-- Source: base/stream.jl:2377-2381 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # BufferStream counterparts of the owner-carrying LibuvStream write
-- # methods, which must not apply here (they track uv requests and the send
-- # buffer; a BufferStream write is in-memory, so no request can outlive the
-- # caller). These writes cannot block for long (the advisory lock's park
-- # runs under the ambient scope): an explicit token gates at entry only.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2382-2387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::BufferStream, a::Vector{UInt8}; cancel::CancelTokenArg=DEFAULT_CANCEL)
    precheck_cancel_arg(cancel)
    GC.@preserve a begin
        return Int(unsafe_write(s, pointer(a), UInt(sizeof(a))))
    end
end
```
-/
def bufferWriteVector {World Stream A Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (unsafeWrite : Stream → BytePointer → U → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  let _ ← precheck cancel
  let pointer ← pointer value
  let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
  JuliaLean.base.iostream.toInt (← unsafeWrite stream pointer size)

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
-/
def bufferWriteString {World Stream A Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token))
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (unsafeWrite : Stream → BytePointer → U → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  let _ ← precheck cancel
  let pointer ← pointer value
  let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
  JuliaLean.base.iostream.toInt (← unsafeWrite stream pointer size)

/--
Julia source: base/stream.jl:2395-2403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(s::BufferStream, a::Array; cancel::CancelTokenArg=DEFAULT_CANCEL)
    precheck_cancel_arg(cancel)
    if isbitstype(eltype(a))
        GC.@preserve a begin
            return Int(unsafe_write(s, Ptr{UInt8}(pointer(a)), UInt(sizeof(a))))
        end
    end
    return invoke(write, Tuple{IO, AbstractArray}, s, a)
end
```
-/
def bufferWriteArray {World Stream A Token : Type}
    (precheck : CancelArg Token → M World (CancelArg Token)) (isBits : A → M World Bool)
    (pointer : A → M World BytePointer) (sizeof : A → M World I)
    (unsafeWrite : Stream → BytePointer → U → M World I) (fallback : Stream → A → M World I)
    (stream : Stream) (value : A) (cancel : CancelArg Token) : M World I := do
  let _ ← precheck cancel
  if ← isBits value then
    let pointer ← pointer value
    let size ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (← sizeof value).val)
    return (← JuliaLean.base.iostream.toInt (← unsafeWrite stream pointer size))
  fallback stream value

/--
Julia source: base/stream.jl:2404-2414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_write(s::BufferStream, p::Ptr{UInt8}, nb::UInt; cancel::CancelTokenArg=DEFAULT_CANCEL)
    # entry gate only (see the BufferStream `write` methods above)
    precheck_cancel_arg(cancel)
    nwrite = lock(s.cond) do
        check_open(s)
        rv = unsafe_write(s.buffer, p, nb)
        s.buffer_writes || notify(s.cond)
        rv
    end
    return nwrite
end
```
-/
def bufferUnsafeWrite {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token)) (checkOpen : Stream → M World Unit)
    (stream : Stream) (pointer : BytePointer) (count : U) (cancel : CancelArg Token) : M World I := do
  let _ ← precheck cancel
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    checkOpen stream
    let count ← buffers.unsafeWrite (← access.get stream).buffer pointer count
    if !(← access.get stream).bufferWrites then ops.notify (← access.get stream).condition
    pure count)

-- UNTRANSLATED
-- Source: base/stream.jl:2415-2415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2416-2424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eof(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    tok = resolve_cancel_token(precheck_cancel_arg(cancel))
    bytesavailable(s) > 0 && return false
    iseof = lock(s.cond) do
        wait_readnb(s, 1, tok)
        return !isopen(s) && bytesavailable(s) <= 0
    end
    return iseof
end
```
-/
def bufferEOF {World Stream Buffer Condition Lock Vector Data Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitRead : Stream → I → Option Token → M World Unit)
    (stream : Stream) (cancel : CancelArg Token) : M World Bool := do
  let token ← resolve (← precheck cancel)
  if (← bufferBytesavailable access buffers stream).val > 0 then return false
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    waitRead stream (i 1) token
    if !(← bufferIsopen access stream) then
      pure ((← bufferBytesavailable access buffers stream).val ≤ 0)
    else pure false)

-- UNTRANSLATED
-- Source: base/stream.jl:2425-2426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # If buffer_writes is called, it will delay notifying waiters till a flush is called.
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2427-2427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
buffer_writes(s::BufferStream, bufsize=0) = (s.buffer_writes = true; s)
```
-/
def bufferEnableWrites {World Stream Buffer Condition Lock N : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (stream : Stream) (_size : N) : M World Stream := do
  access.set stream { (← access.get stream) with bufferWrites := true }
  pure stream

/--
Julia source: base/stream.jl:2428-2436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function flush(s::BufferStream; cancel::CancelTokenArg=DEFAULT_CANCEL)
    # in-memory flush (a notify), nothing to wait for: entry gate only
    precheck_cancel_arg(cancel)
    lock(s.cond) do
        check_open(s)
        notify(s.cond)
        nothing
    end
end
```
-/
def bufferFlush {World Stream Buffer Condition Lock Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token)) (checkOpen : Stream → M World Unit)
    (stream : Stream) (cancel : CancelArg Token) : M World Unit := do
  let _ ← precheck cancel
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    checkOpen stream
    ops.notify (← access.get stream).condition)

-- UNTRANSLATED
-- Source: base/stream.jl:2437-2437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2438-2438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
skip(s::BufferStream, n) = skip(s.buffer, n)
```
-/
def bufferSkip {World Stream Buffer Condition Lock N Result : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (skip : Buffer → N → M World Result) (stream : Stream) (count : N) : M World Result := do
  skip (← access.get stream).buffer count

-- UNTRANSLATED
-- Source: base/stream.jl:2439-2439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source
-- Reason: Documentation, declarations, constants or platform guards; no method body.

/--
Julia source: base/stream.jl:2440-2446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reseteof(s::BufferStream)
    lock(s.cond) do
        s.status = StatusOpen
        nothing
    end
    nothing
end
```
-/
def bufferResetEOF {World Stream Buffer Condition Lock Token : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (ops : ConditionOps World Condition Token) (stream : Stream) : M World Unit := do
  withLock ops.lock ops.unlock (← access.get stream).condition (do
    access.set stream { (← access.get stream) with status := statusOpen })


/-- Project the common libuv handle, status and condition fields. -/
def uvMetadata {World Stream Buffer Condition Lock : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock)) : Metadata World Stream Condition where
  handle := fun stream => do pure (← access.get stream).handle
  status := fun stream => do pure (← access.get stream).status
  setHandle := fun stream handle => do access.set stream { (← access.get stream) with handle }
  setStatus := fun stream status => do access.set stream { (← access.get stream) with status }
  condition := fun stream => do pure (← access.get stream).condition

/-- BufferStream instantiates generic IO using its source methods. Positioning
operations are the independently selected Julia methods for the stream type. -/
def bufferIOOps {World Stream Buffer Condition Lock Vector Data Token Ref : Type}
    (access : Access World Stream (BufferFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (newRef : Byte → M World Ref) (refPointer : Ref → M World BytePointer)
    (position : Stream → M World I) (seek : Stream → I → M World Unit)
    (seekend : Stream → M World Unit) : JuliaLean.base.io.Ops World Stream := Id.run do
  let waitRead := bufferWaitRead access buffers ops
  let opened := bufferIsopen access
  let checked := checkOpen (fun stream => do pure (← access.get stream).status) opened
  return {
    readByte := fun stream => bufferReadByte access buffers ops precheck resolve waitRead stream .default
    writeByte := bufferWriteByte newRef (fun stream reference => do
      bufferUnsafeWrite access buffers ops precheck checked stream (← refPointer reference) (u 1) .default)
    eof := fun stream => bufferEOF access buffers ops precheck resolve waitRead stream .default
    bytesavailable := bufferBytesavailable access buffers
    position := position
    seek := seek
    seekend := seekend
    getMark := fun stream => do pure (← buffers.fields.get (← access.get stream).buffer).mark
    setMark := fun stream mark => do
      let buffer := (← access.get stream).buffer
      buffers.fields.set buffer { (← buffers.fields.get buffer) with mark }
    isopen := opened
    close := bufferClose access ops
    isreadable := bufferIsreadable access buffers
    iswritable := bufferIswritable access buffers }

/-- The libuv adapter keeps kernel operations and waits as typed runtime callees. -/
def libuvIOOps {World Stream Buffer Condition Lock Vector Data Token Ref : Type}
    (access : Access World Stream (UVFields Buffer Condition Lock))
    (buffers : BufferOps World Buffer Vector Data) (ops : ConditionOps World Condition Token)
    (precheck : CancelArg Token → M World (CancelArg Token))
    (resolve : CancelArg Token → M World (Option Token))
    (waitRead : Stream → I → Option Token → M World Unit)
    (beginIO endIO : M World Unit) (nativeReadable nativeWritable : Handle → M World CInt)
    (writeBufferByte : Buffer → Byte → M World I)
    (newRef : Byte → M World Ref) (refPointer : Ref → M World BytePointer)
    (writeOwned : Stream → BytePointer → U → CancelArg Token → Option Ref → Bool → M World I)
    (forceClose closeHandle : Handle → M World Unit) (preserve unpreserve : Stream → M World Unit)
    (position : Stream → M World I) (seek : Stream → I → M World Unit)
    (seekend : Stream → M World Unit) : JuliaLean.base.io.Ops World Stream := Id.run do
  let metadata := uvMetadata access
  let opened := isopen metadata
  let available := bytesavailable access buffers.available
  let readable := isreadable access available opened nativeReadable
  let writable := iswritable access opened nativeWritable
  let eof := eof access precheck resolve available waitRead readable
  let waitClose := waitClose metadata ops preserve unpreserve opened
  return {
    readByte := fun stream => readByte access buffers precheck beginIO endIO eof stream .default
    writeByte := writeByte access buffers beginIO endIO writeBufferByte newRef refPointer writeOwned
    eof := fun stream => eof stream .default
    bytesavailable := available
    position := position
    seek := seek
    seekend := seekend
    getMark := fun stream => do pure (← buffers.fields.get (← access.get stream).buffer).mark
    setMark := fun stream mark => do
      let buffer := (← access.get stream).buffer
      buffers.fields.set buffer { (← buffers.fields.get buffer) with mark }
    isopen := opened
    close := close metadata beginIO endIO forceClose closeHandle opened waitClose
    isreadable := readable
    iswritable := writable }

structure UVWriteOps (World Stream Task Entry Source Owner Queue Result Token : Type) where
  request : RequestOps World Task Entry Source Stream Owner Queue Result
  sourceOf : Option Token → Option Source
  requireSource : Option Source → M World Source
  sourceCancelled : Source → M World Bool
  writeAsync : Stream → BytePointer → U → U → M World (Handle × U × Option (List Handle))
  sourceEnqueue : Source → Byte → Entry → Bool → M World Unit
  sourceRecheck : Source → Byte → Entry → M World Bool
  disarm : Task → Entry → M World Bool
  cancelSeverity : Option Source → M World Byte
  cancellation : Error → Option Byte
  wait : M World Result
  assertCount : Result → M World U
  nwritten : Handle → M World U
  findWitness : Entry → Stream → M World I
  findSource : Entry → Source → M World I
  witnessSlot : Entry → M World I
  getAux : Entry → I → M World U
  setAux : Entry → I → U → M World Unit
  cancelledStatus : CInt
  scheduleCount : Task → U → M World Unit
  scheduleError : Task → Error → M World Unit
  uvError : String → CInt → Error
  signalDepth : M World I
  restoreSignalDepth : I → M World Unit

/-- Julia's exception frame restores the saved sigatomic depth before entering its handler. -/
def withSignalCatch {World A : Type} (depth : M World I) (restore : I → M World Unit)
    (action : M World A) (handler : Error → M World A) : M World A := do
  let saved ← depth
  tryCatch action (fun error => do restore saved; handler error)

/--
Julia source: base/stream.jl:1576-1602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _end_split_uvreq_wait!(w::WaitEntry, @nospecialize(witness), uvw::Ptr{Cvoid},
                                others::Vector{Ptr{Cvoid}}, trycancel::Bool,
                                @nospecialize(owner))
    ct = current_task()
    nwritten::Csize_t = 0
    for j in (lastindex(others) + 1):-1:firstindex(others)
        req = j > lastindex(others) ? uvw : others[j]
        if uv_req_data(req) == C_NULL
            nwritten += ccall(:uv_write_nwritten, Csize_t, (Ptr{Cvoid},), req)
            Libc.free(req)
        else
            trycancel && ccall(:uv_cancel, Cint, (Ptr{Cvoid},), req) # ignore any errors
            uv_req_set_data(req, UV_REQ_DETACHED)
            _root_detached_uvreq!(req, owner)
        end
    end
    _clear_wait_witness!(w, witness)
    @atomicreplace ct.waiting_on w => nothing
    # Drop a claimed-and-enqueued wake an interrupted teardown will never
    # consume (cf. _end_uvreq_wait!).
    q = ct.queue
    q === nothing || list_deletefirst!(q::StickyWorkqueue, ct)
    iolock_end()
    sigatomic_end()
    unpreserve_handle(ct)
    return nwritten
end
```
-/
def endSplitUVRequestWait {World Task Entry Source Witness Owner Queue Result : Type}
    (p : RequestOps World Task Entry Source Witness Owner Queue Result) (nwritten : Handle → M World U)
    (entry : Entry) (witness : Witness) (request : Handle) (others : List Handle)
    (trycancel : Bool) (owner : Option Owner) : M World U := do
  let task ← p.currentTask
  let mut written := u 0
  for request in request :: others.reverse do
    if (← p.data request).address.val == 0 then
      written := written + (← nwritten request)
      p.free request
    else
      if trycancel then let _ ← p.cancel request
      p.setData request ⟨u 1⟩
      p.rootDetached request owner
  p.clearWitness entry witness
  let _ ← p.replaceWaiting .sequentiallyConsistent .sequentiallyConsistent task (some entry) none
  match ← p.queue task with
  | none => pure ()
  | some queue => p.deleteFirst queue task
  p.endIO
  p.sigatomicEnd
  p.unpreserve task
  pure written

/--
Julia source: base/stream.jl:1478-1555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uv_write_cancelled_finish(s::LibuvStream, w::WaitEntry, uvw::Ptr{Cvoid},
                                    sev::UInt8, src::CancellationTokenSource,
                                    @nospecialize(owner),
                                    others::Union{Nothing, Vector{Ptr{Cvoid}}})
    ct = current_task()
    nwritten::Csize_t = 0
    awaited = false
    iolock_begin()
    if others === nothing ? uv_req_data(uvw) == C_NULL : _split_complete(uvw, others)
        # the completion callback(s) already ran (the wake lost its claim
        # race): the requests are ours and know their counts
        awaited = true
        if others === nothing
            nwritten = ccall(:uv_write_nwritten, Csize_t, (Ptr{Cvoid},), uvw)
        end
    else
        # The write is still in flight: flag it as cancelled-by-us first
        # (on the witness slot's aux, under the iolock), so the completion
        # callback(s) can tell our UV_ECANCELED from a close-induced one -
        # see uv_writecb_task - then sweep, tail-first.
        _mark_uvreq_cancel_requested!(w, s)
        uv_req_data(uvw) == C_NULL ||
            ccall(:uv_cancel, Cint, (Ptr{Cvoid},), uvw) # ignore any errors
        if others !== nothing
            for j in lastindex(others):-1:firstindex(others)
                r = others[j]
                uv_req_data(r) == C_NULL ||
                    ccall(:uv_cancel, Cint, (Ptr{Cvoid},), r) # ignore any errors
            end
        end
        if sev < severity(CANCEL_REQUEST_ABANDON_EXTERNAL)
            # SAFE cancellation: await the completion callback, so that the
            # caller's buffer is provably no longer in use when this
            # returns. Only a severity escalation may interrupt this bounded
            # teardown wait: stage the raised eligibility floor, then re-arm
            # the (still registered) entry - the re-park needs no new
            # registration.
            slots(w)[_find_slot(w, src)].aux = UInt64(sev + 0x01)
            sw = SourceWait(src, UInt8(sev + 0x01))
            _arm_wait(ct, w)
            wait_enqueue!(sw, w, false)  # sticky: the seq_cst re-arm fence
            if !(wait_recheck(sw, w) && disarm!(ct, w))
                iolock_end()
                try
                    nwritten = wait()::Csize_t
                    awaited = true
                catch
                    # escalated (or interrupted) during the teardown wait:
                    # fall through to detach
                end
                iolock_begin()
                if !awaited &&
                   (others === nothing ? uv_req_data(uvw) == C_NULL :
                                         _split_complete(uvw, others))
                    # the callback(s) ran anyway (our wake lost a race)
                    awaited = true
                    if others === nothing
                        nwritten = ccall(:uv_write_nwritten, Csize_t, (Ptr{Cvoid},), uvw)
                    end
                end
            end
            # (a refused registration means the state already escalated)
        end
    end
    # Resolve ownership. Awaited or not, completed requests are ours (a
    # split write sums their exact counts); anything still in flight - an
    # abandoning severity, or an escalation during the teardown wait - is
    # detached for its callback to free, with the written buffer kept
    # rooted until every detached callback has run; those requests' counts
    # are unknown and contribute 0. (No re-cancel: the sweep above already
    # cancelled everything that was in flight.)
    if others === nothing
        _end_uvreq_wait!(w, s, uvw, false, owner)
    else
        nwritten = _end_split_uvreq_wait!(w, s, uvw, others, false, owner)
    end
    return nwritten
end
```
-/
def uvWriteCancelledFinish {World Stream Task Entry Source Owner Queue Result Token : Type}
    (p : UVWriteOps World Stream Task Entry Source Owner Queue Result Token)
    (stream : Stream) (entry : Entry) (request : Handle) (severity : Byte) (source : Source)
    (owner : Option Owner) (others : Option (List Handle)) : M World U := do
  let task ← p.request.currentTask
  let mut written := u 0
  let mut awaited := false
  p.request.beginIO
  let complete ← match others with
    | none => pure ((← p.request.data request).address.val == 0)
    | some others => splitComplete p.request.data request others
  if complete then
    awaited := true
    if others.isNone then written ← p.nwritten request
  else
    markUVRequestCancelled p.findWitness p.getAux p.setAux entry stream
    if (← p.request.data request).address.val != 0 then let _ ← p.request.cancel request
    match others with
    | none => pure ()
    | some others =>
      for request in others.reverse do
        if (← p.request.data request).address.val != 0 then let _ ← p.request.cancel request
    if severity.val < 3 then
      let floor := severity + JuliaLean.base.io.byte 1
      let slot ← p.findSource entry source
      p.setAux entry slot (u floor.val)
      p.request.arm task entry
      p.sourceEnqueue source floor entry false
      let refused ← if ← p.sourceRecheck source floor entry then p.disarm task entry else pure false
      if !refused then
        p.request.endIO
        let result ← withSignalCatch p.signalDepth p.restoreSignalDepth
          (do pure (Except.ok (← p.assertCount (← p.wait))))
          (fun error => pure (Except.error error))
        match result with
        | .ok count => written := count; awaited := true
        | .error _ => pure ()
        p.request.beginIO
        if !awaited then
          let complete ← match others with
            | none => pure ((← p.request.data request).address.val == 0)
            | some others => splitComplete p.request.data request others
          if complete then
            awaited := true
            if others.isNone then written ← p.nwritten request
  match others with
  | none => endUVRequestWait p.request entry stream request false owner
  | some others => written ← endSplitUVRequestWait p.request p.nwritten entry stream request others false owner
  pure written

/--
Julia source: base/stream.jl:1360-1464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _uv_write_wait(s::LibuvStream, p::Ptr{UInt8}, n::UInt,
                        tok::MaybeToken, @nospecialize(owner), partial::Bool,
                        chunk::UInt=MAX_OS_WRITE)
    src = cancel_source(tok)
    # entry check: throw before handing anything to libuv
    _iolocked_checkcancel(src)
    local uvw, lastn, others
    try
        uvw, lastn, others = uv_write_async(s, p, n, chunk)
    catch
        # E.g. the stream was (or gets) closed: release the iolock so that
        # errors propagate without it.
        iolock_end()
        rethrow()
    end
    w = _begin_uvreq_wait!(src, s, uvw)
    if others !== nothing
        # A split write: point every chunk request at the wait entry and
        # store the pending-callback count on the witness slot's aux (all
        # under the iolock hold that covers submission, so no callback can
        # have run yet). Completions count down; only the last claims and
        # wakes. The waiter owns - and, once all callbacks have run, sums
        # and frees - every chunk request, which is what makes the total
        # accepted-byte count exact even when a cancellation sweep
        # completes the requests out of order.
        wp = pointer_from_objref(w)
        for r in others
            uv_req_set_data(r, wp)
        end
        i = _find_slot(w, s)
        _set_slot_aux!(w, i, _slot_aux(w, i) |
                       (UInt64(length(others) + 1) << _UVREQ_AUX_PENDING_SHIFT))
    end
    refused = false
    if src !== nothing
        sw = SourceWait(src, 0x00)
        wait_enqueue!(sw, w, false)
        # a lost self-claim means a concurrent walk claimed the freshly
        # armed entry: its wake delivers the request into the park below
        refused = wait_recheck(sw, w) && disarm!(current_task(), w)
    end
    if refused
        # The token was cancelled since the entry check and the recheck's
        # self-claim won the wake back: don't park. Resolve the in-flight
        # write and report the bytes that reached the OS; the caller
        # observes the cancellation at its next cancellation point.
        iolock_end()
        nwritten = _uv_write_cancelled_finish(s, w, uvw,
            severity(cancel_severity(src)::CancellationRequest), src, owner, others)
        # level-triggered: the throw below (and any later cancellation
        # point) reads the current severity
        partial || checkcancel(src)
        return others === nothing ? Int(n - lastn + nwritten) : Int(nwritten)
    end
    iolock_end()
    local nwritten::Csize_t
    creq = nothing
    try
        sigatomic_end()
        # wait for the write to complete (or error): the last request's
        # callback for a single-request write, the pending count reaching
        # zero for a split one (whose wake also carries the first real
        # error of any chunk)
        nwritten = wait()::Csize_t
        sigatomic_begin()
    catch err
        # (catch restored the sigatomic level from the try entry)
        if err isa CancellationRequest
            # Cancellation is an expected outcome of a write, not an error:
            # resolve the request's ownership below and return the partial
            # count - the caller's next cancellation point (re)delivers the
            # request. (The delivery is level-triggered, so nothing is
            # lost by not propagating this throw.)
            creq = err
        else
            # interrupted by something other than a cancellation (an
            # interrupter or raw throwto): cancel whatever is still
            # cancellable and detach the rest to the callbacks
            iolock_begin()
            if others === nothing
                _end_uvreq_wait!(w, s, uvw, true, owner)
            else
                _end_split_uvreq_wait!(w, s, uvw, others, true, owner)
            end
            rethrow()
        end
    end
    if creq !== nothing
        nwritten = _uv_write_cancelled_finish(s, w, uvw, severity(creq), src, owner, others)
        # the in-flight request is resolved (SAFE: the buffer is provably
        # out of OS hands); deliver the cancellation now unless the caller
        # asked for the partial count
        partial || checkcancel(src::CancellationTokenSource)
    else
        # normal completion (or the wake lost the race to a completion that
        # ran anyway): the callback(s) handed us the request(s) to free
        iolock_begin()
        if others === nothing
            _end_uvreq_wait!(w, s, uvw, true, owner)
        else
            nwritten = _end_split_uvreq_wait!(w, s, uvw, others, false, owner)
        end
    end
    return others === nothing ? Int(n - lastn + nwritten) : Int(nwritten)
end
```
-/
def uvWriteWait {World Stream Task Entry Source Owner Queue Result Token : Type}
    (p : UVWriteOps World Stream Task Entry Source Owner Queue Result Token)
    (stream : Stream) (pointer : BytePointer) (count : U) (token : Option Token)
    (owner : Option Owner) (partialWrite : Bool) (chunk : U) : M World I := do
  let source := p.sourceOf token
  iolockedCheckcancel p.sourceCancelled p.request.endIO (fun source => p.request.checkCancel (some source)) source
  let (request, lastCount, others) ← tryCatch (p.writeAsync stream pointer count chunk) (fun error => do
    p.request.endIO
    throw error)
  let entry ← beginUVRequestWait p.request source stream request
  match others with
  | none => pure ()
  | some others =>
    let pointer ← p.request.entryPointer entry
    for request in others do p.request.setData request pointer
    let slot ← p.findWitness entry stream
    let length := i (others.length : Int) + i 1
    let pending ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 length.val)
    p.setAux entry slot (JuliaLean.base.int.or_int (← p.getAux entry slot) (JuliaLean.base.int.shl_int pending (i 32)))
  let refused ← match source with
    | none => pure false
    | some source => do
      p.sourceEnqueue source (JuliaLean.base.io.byte 0) entry false
      if ← p.sourceRecheck source (JuliaLean.base.io.byte 0) entry then
        p.disarm (← p.request.currentTask) entry
      else pure false
  if refused then
    p.request.endIO
    let severity ← p.cancelSeverity source
    let written ← uvWriteCancelledFinish p stream entry request severity (← p.requireSource source) owner others
    if !partialWrite then p.request.checkCancel source
    JuliaLean.base.iostream.toInt (if others.isNone then count - lastCount + written else written)
  else
    p.request.endIO
    let outcome ← withSignalCatch p.signalDepth p.restoreSignalDepth (do
      p.request.sigatomicEnd
      let written ← p.assertCount (← p.wait)
      p.request.sigatomicBegin
      pure (Except.ok written)) (fun error => pure (Except.error error))
    let (written, cancellation) ← match outcome with
      | .ok written => pure (written, none)
      | .error error =>
        match p.cancellation error with
        | some severity => pure (u 0, some severity)
        | none => do
          p.request.beginIO
          match others with
          | none => endUVRequestWait p.request entry stream request true owner
          | some others => let _ ← endSplitUVRequestWait p.request p.nwritten entry stream request others true owner; pure ()
          throw error
    let written ← match cancellation with
      | some severity => do
        let written ← uvWriteCancelledFinish p stream entry request severity (← p.requireSource source) owner others
        if !partialWrite then
          let concrete ← p.requireSource source
          p.request.checkCancel (some concrete)
        pure written
      | none => do
        p.request.beginIO
        match others with
        | none => endUVRequestWait p.request entry stream request true owner; pure written
        | some others => endSplitUVRequestWait p.request p.nwritten entry stream request others false owner
    JuliaLean.base.iostream.toInt (if others.isNone then count - lastCount + written else written)

/--
Julia source: base/stream.jl:1856-1907 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function uv_writecb_task(req::Ptr{Cvoid}, status::Cint)
    # A chunk of a waited *split* write counts down on the witness slot's
    # aux instead of waking: the waiter owns (and later frees) every chunk
    # request, so the callback only records completion (data = C_NULL) and
    # any first real error; the callback that brings the count to 0 falls
    # through to the ordinary claim-and-wake below.
    d = uv_req_data(req)
    if d != C_NULL && d != UV_REQ_DETACHED
        w = unsafe_pointer_to_objref(d)::WaitEntry
        i = _uvreq_witness_slot(w)
        if i != 0
            aux = _slot_aux(w, i)
            pending = aux >> _UVREQ_AUX_PENDING_SHIFT
            if pending > 1
                uv_req_set_data(req, C_NULL)
                if status != 0 &&
                   !(status == UV_ECANCELED && aux & _UVREQ_AUX_CANCEL_REQUESTED != 0) &&
                   aux & _UVREQ_AUX_STATUS_MASK == 0
                    aux |= (UInt64(-status) << _UVREQ_AUX_STATUS_SHIFT) & _UVREQ_AUX_STATUS_MASK
                end
                _set_slot_aux!(w, i, (aux & ~(typemax(UInt64) << _UVREQ_AUX_PENDING_SHIFT)) |
                                     ((pending - 1) << _UVREQ_AUX_PENDING_SHIFT))
                return nothing
            end
            # pending == 1: final chunk of a split write - a real error
            # recorded by an earlier chunk must win the wake even if this
            # chunk itself completed cleanly (or with the expected
            # UV_ECANCELED of a cancellation sweep)
            if pending == 1 && aux & _UVREQ_AUX_STATUS_MASK != 0
                status = Cint(-((aux & _UVREQ_AUX_STATUS_MASK) >> _UVREQ_AUX_STATUS_SHIFT))
            end
        end
    end
    # An expected-by-the-waiter UV_ECANCELED must be read off the entry
    # before the claim below releases the witness slot.
    cancel_requested = status == UV_ECANCELED && _uvreq_cancel_requested(req)
    t = _claim_uvreq_waiter(req)
    if t !== nothing
        if status == 0 || cancel_requested
            # For writes cancelled by the waiter, this is the partial write
            # count. (For a split write the value is ignored: the waiter
            # recomputes the total from the chunk requests it owns.)
            schedule(t, ccall(:uv_write_nwritten, Csize_t, (Ptr{Cvoid},), req))
        else
            # A real error - including a close-induced UV_ECANCELED (libuv
            # fails still-queued writes with it when the stream closes),
            # which must not masquerade as a benign short write.
            schedule(t, _UVError("write", status); error=true)
        end
    end
    nothing
end
```
-/
def uvWriteCallback {World Stream Task Entry Source Owner Queue Result Token : Type}
    (p : UVWriteOps World Stream Task Entry Source Owner Queue Result Token) (request : Handle) (initialStatus : CInt) : M World Unit := do
  let data ← p.request.data request
  let (status, finished) ← (fun (seed : CInt) => do
    let mut status := seed
    if data.address.val != 0 && data.address.val != 1 then
      let entry ← p.request.pointerEntry data
      let slot ← p.witnessSlot entry
      if slot.val != 0 then
        let mut aux ← p.getAux entry slot
        let pending := JuliaLean.base.int.lshr_int aux (i 32)
        let mask := JuliaLean.base.int.shl_int (u 0xffff) (i 8)
        if pending.val > 1 then
          p.request.setData request nullHandle
          let requested := (JuliaLean.base.int.and_int aux (u 1)).val != 0
          if status.val != 0 && !(status.val == p.cancelledStatus.val && requested) && (JuliaLean.base.int.and_int aux mask).val == 0 then
            let error ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.u64.name) .u64 (JuliaLean.base.int.neg_int status).val)
            aux := JuliaLean.base.int.or_int aux (JuliaLean.base.int.and_int (JuliaLean.base.int.shl_int error (i 8)) mask)
          let low := JuliaLean.base.int.and_int aux (JuliaLean.base.int.not_int (JuliaLean.base.int.shl_int (u 18446744073709551615) (i 32)))
          p.setAux entry slot (JuliaLean.base.int.or_int low (JuliaLean.base.int.shl_int (pending - u 1) (i 32)))
          return (status, true)
        if pending.val == 1 && (JuliaLean.base.int.and_int aux mask).val != 0 then
          let encoded := JuliaLean.base.int.neg_int (JuliaLean.base.int.lshr_int (JuliaLean.base.int.and_int aux mask) (i 8))
          status ← JuliaLean.base.io.liftJl (JInt.convert (IntTy.i32.name) .i32 encoded.val)
    pure (status, false)) initialStatus
  if finished then return ()
  let requested ← if status.val == p.cancelledStatus.val then
      uvreqCancelRequested p.request.data p.request.pointerEntry p.witnessSlot p.getAux request
    else pure false
  match ← claimUVRequestWaiter p.request request with
  | none => pure ()
  | some task =>
    if status.val == 0 || requested then p.scheduleCount task (← p.nwritten request)
    else p.scheduleError task (p.uvError "write" status)

end JuliaLean.base.stream

namespace JuliaLean.Streams

open JuliaLean

/-- A newly initialized readable and writable stream. -/
def freshStream (kind : StreamKind) : StreamM :=
  { kind, status := .active, buffer := [], writable := true }

/-- `close`, `base/iostream.jl:90-93`, `base/stream.jl:770-783,2231-2236`. -/
def closeStream (s : StreamM) : StreamM := { s with status := .closed }

/-- `eof`: buffered data prevents EOF even after close (`base/io.jl:208-215`),
as implemented for libuv streams at `base/stream.jl:104-115,2416-2422`. -/
def streamEof (s : StreamM) : Bool :=
  s.buffer.isEmpty && (s.status == .eof || s.status == .closed)

/-- `unsafe_write` and the byte `write` specialization. For a pipe this updates
the connected reader's logical queue; for an `IOStream` it updates the logical
file contents later exposed by rewinding. Closed IOStreams fail the
`iswritable` guard (`base/iostream.jl:411-425`). Libuv-backed methods call
`check_open` (`base/stream.jl:384-388,1736-1739,2404-2413`). -/
def unsafeWrite (s : StreamM) (memory : List UInt8) (n : Nat) : SR (Nat × StreamM) :=
  if n > memory.length then .error .invalidPointer
  else
    match s.kind with
    | .ioStream =>
        if !isWritable s then .error .argumentError
        else .ok (n, { s with buffer := s.buffer ++ memory.take n })
    | .libuvStream =>
        if !isWritable s then .error .ioError
        else .ok (n, s)
    | .bufferStream =>
        if !isWritable s then .error .ioError
        else .ok (n, { s with buffer := s.buffer ++ memory.take n })

def writeBytes (s : StreamM) (bytes : List UInt8) : SR (Nat × StreamM) :=
  unsafeWrite s bytes bytes.length

/-- The two endpoints created by `Pipe()`/`link_pipe!`,
`base/stream.jl:1048-1118`. -/
structure PipeM where
  readEnd : StreamM
  writeEnd : StreamM
  deriving Repr, DecidableEq

def freshPipe : PipeM :=
  { readEnd := freshStream .libuvStream, writeEnd := freshStream .libuvStream }

/-- Writing one PipeEndpoint appends to its connected peer's receive queue. -/
def pipeWrite (p : PipeM) (bytes : List UInt8) : SR (Nat × PipeM) :=
  if !isWritable p.writeEnd then .error .ioError
  else .ok (bytes.length,
    { p with readEnd := { p.readEnd with buffer := p.readEnd.buffer ++ bytes } })

/-- `closewrite(pipe)` closes the writer direction and delivers EOF to the
reader after the queued bytes, `base/stream.jl:719-747,1076`. -/
def closePipeWrite (p : PipeM) : PipeM :=
  { readEnd := { p.readEnd with status := .eof },
    writeEnd := { p.writeEnd with writable := false } }

/-- Exact-length `unsafe_read`, `base/iostream.jl:477-483` and
`base/stream.jl:1240-1275,2249-2255`. -/
def unsafeRead (s : StreamM) (n : Nat) : SR (List UInt8 × StreamM) :=
  if n ≤ s.buffer.length then
    .ok (s.buffer.take n, { s with buffer := s.buffer.drop n })
  else .error .eofError

/-- `readavailable`, `base/iostream.jl:431-442` and
`base/stream.jl:1292-1300,2277-2287`. -/
def readAvailable (s : StreamM) : SR (List UInt8 × StreamM) :=
  .ok (s.buffer, { s with buffer := [] })
/-- `readuntil`/`copyuntil` delimiter handling for a completed read,
`base/stream.jl:1302-1344,2339-2360` and `base/iostream.jl:490-503`. -/
def readUntil (s : StreamM) (delim : UInt8) (keep : Bool) : SR (List UInt8 × StreamM) :=
  let r := splitUntil delim s.buffer
  let bytes := if r.found && keep then r.before ++ [delim] else r.before
  .ok (bytes, { s with buffer := r.after })

end JuliaLean.Streams

namespace JuliaLean.Streams

open JuliaLean

/-! ## `base/stream.jl`: handle lifecycle and request ownership -/

inductive UvStatus where
  | uninit | init | connecting | opened | active | closing | closed | eof | paused
  deriving Repr, DecidableEq

def uvStatusString (hasHandle : Bool) (status : UvStatus) : String :=
  if !hasHandle then
    match status with
    | .closed => "closed"
    | .uninit => "null"
    | _ => "invalid status"
  else
    match status with
    | .uninit => "uninit"
    | .init => "init"
    | .connecting => "connecting"
    | .opened => "open"
    | .active => "active"
    | .paused => "paused"
    | .closing => "closing"
    | .closed => "closed"
    | .eof => "eof"

structure EndpointM where
  hasHandle : Bool
  status : UvStatus
  buffer : List UInt8
  readError : Bool
  sendBuffer : Option (List UInt8)
  readable : Bool
  writable : Bool
  throttle : Nat
  preserved : Nat
  deriving Repr, DecidableEq

def endpointCtor (hasHandle : Bool) (status : UvStatus) : EndpointM :=
  { hasHandle, status, buffer := [], readError := false, sendBuffer := none,
    readable := true, writable := true, throttle := 10 * 1024 * 1024,
    preserved := 0 }

inductive EndpointField where | handle | status | buffer | readable | writable | throttle
  deriving Repr, DecidableEq

def endpointField (s : EndpointM) : EndpointField → Nat
  | .handle => if s.hasHandle then 1 else 0
  | .status => match s.status with
    | .uninit => 0 | .init => 1 | .connecting => 2 | .opened => 3 | .active => 4
    | .closing => 5 | .closed => 6 | .eof => 7 | .paused => 8
  | .buffer => s.buffer.length
  | .readable => if s.readable then 1 else 0
  | .writable => if s.writable then 1 else 0
  | .throttle => s.throttle

def endpointShow (typeName : String) (fd : Int) (s : EndpointM) : String :=
  typeName ++ "(" ++ toString fd ++ " " ++ uvStatusString s.hasHandle s.status ++
    ", " ++ toString s.buffer.length ++ " bytes waiting)"

def setupStreamStdio (s : EndpointM) : EndpointM × Bool := (s, false)
def rawHandleModel (s : EndpointM) : Bool := s.hasHandle

def lockDepth (depth : Nat) (locking : Bool) : Nat :=
  if locking then depth + 1 else depth - 1

def endpointIsOpen (s : EndpointM) : Except StreamErr Bool :=
  if s.status == .uninit || s.status == .init || !s.hasHandle then
    .error .argumentError
  else .ok (s.status != .closed)

def endpointReadable (s : EndpointM) : Bool :=
  !s.buffer.isEmpty ||
    (s.hasHandle && s.status != .closed && s.status != .eof && s.readable)

def endpointWritable (s : EndpointM) : Bool :=
  s.hasHandle && s.status != .closed && s.status != .closing && s.writable

def endpointCheckOpen (s : EndpointM) : Except StreamErr Unit :=
  match endpointIsOpen s with
  | .ok true => if s.status == .closing then .error .ioError else .ok ()
  | _ => .error .ioError

def waitReadState (s : EndpointM) (needed : Nat) : Except StreamErr EndpointM :=
  if needed ≤ s.buffer.length then .ok s
  else if s.readError then .error .ioError
  else if !s.hasHandle || s.status == .closed || s.status == .eof then .ok s
  else .ok { s with throttle := max needed s.throttle }

def endpointCloseWrite (s : EndpointM) (shutdownStatus : Int) : Except StreamErr EndpointM :=
  if !endpointWritable s then .ok s
  else if shutdownStatus < 0 then .error .ioError
  else .ok { s with writable := false }

def endpointClose (s : EndpointM) : EndpointM :=
  { s with status := .closed, hasHandle := false, readable := false, writable := false }

def displaySizeModel (lines columns : Option Nat) : Nat × Nat :=
  (lines.getD 24, columns.getD 80)

def allocRequestSize (available recommended maximum : Nat) : Nat :=
  min (maximum - available) recommended

def startReadingState (s : EndpointM) : EndpointM :=
  if s.status == .opened || s.status == .paused then { s with status := .active } else s

def stopReadingState (s : EndpointM) : EndpointM :=
  if s.status == .active then { s with status := .paused } else s

def pipeEndpoints (p : PipeM) : StreamM × StreamM := (p.readEnd, p.writeEnd)

def notifyFilled (s : EndpointM) (bytes : List UInt8) (nread : Int) : EndpointM :=
  if nread < 0 then
    let hasError : Bool := decide (nread ≠ (-4095 : Int))
    let nextStatus := if nread == -4095 then UvStatus.eof else s.status
    { s with readError := hasError, status := nextStatus }
  else
    let added := bytes.take nread.toNat
    let nextStatus := if s.status == .paused then UvStatus.opened else s.status
    let nextBuffer := s.buffer ++ added
    { s with buffer := nextBuffer, status := nextStatus }

inductive ReqOwner where | fireAndForget | waiter | detachedReq | callbackDone
  deriving Repr, DecidableEq

structure ReqM where
  owner : ReqOwner
  cancelRequested : Bool
  rooted : Bool
  pending : Nat
  firstError : Option Int
  written : Nat
  deriving Repr, DecidableEq

def beginReq (cancelled : Bool) (splitCount : Nat) : Except StreamErr ReqM :=
  if cancelled then .error .ioError
  else .ok ⟨.waiter, false, false, splitCount, none, 0⟩

def markReqCancelled (r : ReqM) : ReqM := { r with cancelRequested := true }

def finishReq (r : ReqM) (completed : Bool) (tryCancel : Bool) (knownOwner : Bool) : ReqM :=
  if completed then
    ⟨.callbackDone, r.cancelRequested, false, r.pending, r.firstError, r.written⟩
  else
    ⟨.detachedReq, tryCancel, knownOwner, r.pending, r.firstError, r.written⟩

def completeReq (r : ReqM) (status : Int) (nwritten : Nat) : ReqM :=
  let err := if decide (status < 0) && r.firstError.isNone then some status else r.firstError
  let nextPending := r.pending - 1
  let nextWritten := r.written + nwritten
  let nextOwner := if r.pending ≤ 1 then ReqOwner.callbackDone else r.owner
  ⟨nextOwner, r.cancelRequested, r.rooted, nextPending, err, nextWritten⟩

def requeueUnwritten (sent queued : List UInt8) (nwritten : Nat) : List UInt8 :=
  sent.drop nwritten ++ queued

/-! ## Stream reads, writes, redirection, and BufferStream -/

def readbytesModel (buffer : List UInt8) (n : Nat) : Nat × List UInt8 × List UInt8 :=
  let count := min n buffer.length
  (count, buffer.take count, buffer.drop count)

def readUntilModel (buffer : List UInt8) (d : UInt8) (keep : Bool) : List UInt8 × List UInt8 :=
  let r := splitUntil d buffer
  (if r.found && keep then r.before ++ [d] else r.before, r.after)

def peekModel (buffer : List UInt8) (n : Nat) : Except StreamErr (List UInt8) :=
  if n ≤ buffer.length then .ok (buffer.take n) else .error .eofError

def writeChunks (n chunk : Nat) : List Nat :=
  if chunk = 0 then []
  else (List.range ((n + chunk - 1) / chunk)).map fun i => min chunk (n - i * chunk)

inductive RedirectValue where | keep | devnull | path (p : String) | stream
  deriving Repr, DecidableEq

structure RedirectM where
  inStream : RedirectValue
  outStream : RedirectValue
  errStream : RedirectValue
  deriving Repr, DecidableEq

def resolveRedirect (new old : RedirectValue) : RedirectValue :=
  match new with | .keep => old | x => x

def redirectStdio (old : RedirectM) (newIn newOut newErr : RedirectValue) : RedirectM :=
  { inStream := resolveRedirect newIn old.inStream,
    outStream := resolveRedirect newOut old.outStream,
    errStream := resolveRedirect newErr old.errStream }

def samePath (x y : String) : Bool := x == y

def pipeGetindex (p : α × α) (key : Int) : Option α :=
  if key = 1 then some p.1 else if key = 2 then some p.2 else none

def bufferReadByte (s : StreamM) : Except StreamErr (UInt8 × StreamM) :=
  match s.buffer with
  | b :: rest => .ok (b, { s with buffer := rest })
  | [] => .error .eofError

def bufferReadN (s : StreamM) (n : Nat) : List UInt8 × StreamM :=
  (s.buffer.take n, { s with buffer := s.buffer.drop n })

def bufferResetEof (s : StreamM) : StreamM :=
  if s.status == .eof then { s with status := .active } else s

def bufferReadable (s : StreamM) : Bool := isOpen s || !s.buffer.isEmpty
def bufferWritable (s : StreamM) : Bool := isOpen s && s.writable
def bufferClose (s : StreamM) : StreamM := closeStream s
def bufferEof (s : StreamM) : Bool := streamEof s
def bufferSkip (s : StreamM) (n : Nat) : StreamM := { s with buffer := s.buffer.drop n }
def bufferFlush (s : StreamM) : StreamM := s


end JuliaLean.Streams

namespace JuliaLean.Streams.Methods.Stream

open JuliaLean.Streams

structure Args where
  endpoint : EndpointM
  stream : StreamM
  pipe : PipeM
  req : ReqM
  redirect : RedirectM
  bytes : List UInt8
  queued : List UInt8
  n : Nat
  m : Nat
  i : Int
  j : Int
  byte : UInt8
  flag : Bool
  flag2 : Bool
  flag3 : Bool
  status : UvStatus
  field : EndpointField
  handleKind : HandleKind
  text : String
  text2 : String
  deriving Repr, DecidableEq

structure Obs where
  endpoint : EndpointM
  stream : StreamM
  pipe : PipeM
  req : ReqM
  redirect : RedirectM
  bytes : List UInt8
  counts : List Nat
  integer : Int
  flags : List Bool
  text : String
  error : Option StreamErr
  deriving Repr, DecidableEq

def base (a : Args) : Obs :=
  ⟨a.endpoint, a.stream, a.pipe, a.req, a.redirect, a.bytes, [], a.i, [], a.text, none⟩

def withEndpoint (a : Args) : Except StreamErr EndpointM → Obs
  | .ok endpoint => { base a with endpoint }
  | .error error => { base a with error := some error }

def withStream (a : Args) : Except StreamErr (Nat × StreamM) → Obs
  | .ok (count, stream) => { base a with stream, counts := [count] }
  | .error error => { base a with error := some error }

def withRead (a : Args) : Except StreamErr (List UInt8 × StreamM) → Obs
  | .ok (bytes, stream) => { base a with bytes, stream, counts := [bytes.length] }
  | .error error => { base a with error := some error }

def reqFinishObs (a : Args) (completed tryCancel knownOwner : Bool) : Obs :=
  { base a with req := finishReq a.req completed tryCancel knownOwner }

def m29 (a : Args) : Obs := { base a with counts := [endpointField a.endpoint a.field] }

def m58 (a : Args) : Obs := { base a with counts := [endpointField a.endpoint a.field] }

def m102 (a : Args) : Obs := { base a with counts := [a.endpoint.buffer.length] }

def m104 (a : Args) : Obs := { base a with flags := [streamEof a.stream] }

def m139 (a : Args) : Obs := { base a with text := uvStatusString a.endpoint.hasHandle a.status }

def m179 (a : Args) : Obs := { base a with endpoint := endpointCtor a.endpoint.hasHandle a.status }

def m194 (a : Args) : Obs := { base a with endpoint := endpointCtor false .uninit }

def m204 (a : Args) : Obs := { base a with endpoint := endpointCtor a.flag .init }

def m224 (a : Args) : Obs := { base a with endpoint := endpointCtor a.endpoint.hasHandle a.status }

def m244 (a : Args) : Obs := { base a with endpoint := endpointCtor a.flag .init }

def m258 (a : Args) : Obs := { base a with text := endpointShow "LibuvServer" a.i a.endpoint }

def m261 (a : Args) : Obs := { base a with text := endpointShow a.text a.i a.endpoint }

def m268 (a : Args) : Obs := { base a with flags := [endpointReadable a.endpoint] }

def m275 (a : Args) : Obs := { base a with flags := [endpointWritable a.endpoint] }

def m281 (a : Args) : Obs := { base a with counts := [lockDepth a.n true] }

def m282 (a : Args) : Obs := { base a with counts := [lockDepth a.n false] }

def m284 (a : Args) : Obs := { base a with endpoint := (setupStreamStdio a.endpoint).1, flags := [(setupStreamStdio a.endpoint).2] }

def m285 (a : Args) : Obs := { base a with flags := [rawHandleModel a.endpoint] }

def m286 (a : Args) : Obs := { base a with flags := [a.endpoint.hasHandle] }

def m288 (a : Args) : Obs := match initStdioModel a.handleKind with
      | .ok kind => { base a with stream := freshStream kind }
      | .error e => { base a with error := some e }

def m328 (a : Args) : Obs := { base a with endpoint := { a.endpoint with hasHandle := a.flag, status := if a.flag then .opened else .closed } }

def m364 (a : Args) : Obs := { base a with endpoint := { a.endpoint with hasHandle := a.flag, status := if a.flag then .opened else .closed } }

def m377 (a : Args) : Obs := match endpointIsOpen a.endpoint with
      | .ok opened => { base a with flags := [opened] }
      | .error e => { base a with error := some e }

def m384 (a : Args) : Obs := withEndpoint a (match endpointCheckOpen a.endpoint with | .ok _ => .ok a.endpoint | .error e => .error e)

def m390 (a : Args) : Obs := withEndpoint a (waitReadState a.endpoint a.n)

def m493 (a : Args) : Obs := { base a with flags := [a.req.owner == .waiter] }

def m502 (a : Args) : Obs := { base a with req := markReqCancelled a.req }

def m511 (a : Args) : Obs := { base a with flags := [a.req.cancelRequested] }

def m530 (a : Args) : Obs := { base a with req := { a.req with rooted := true, owner := .detachedReq } }

def m534 (a : Args) : Obs := { base a with req := { a.req with rooted := false } }

def m540 (a : Args) : Obs := if a.flag then { base a with error := some .ioError } else base a

def m553 (a : Args) : Obs := match beginReq a.flag a.n with
      | .ok req => { base a with req }
      | .error e => { base a with error := some e }

def m575 (a : Args) : Obs := reqFinishObs a a.flag a.flag2 a.flag3

def m615 (a : Args) : Obs := { base a with flags := [a.flag], counts := [a.n + 1] }

def m626 (a : Args) : Obs := { base a with req := if a.byte = 0 then a.req else markReqCancelled a.req }

def m650 (a : Args) : Obs := reqFinishObs a a.flag a.flag2 a.flag3

def m700 (a : Args) : Obs := { base a with flags := [a.req.owner == .waiter], req := if a.req.owner == .waiter then { a.req with owner := .callbackDone } else a.req }

def m719 (a : Args) : Obs := withEndpoint a (endpointCloseWrite a.endpoint a.i)

def m750 (a : Args) : Obs := { base a with endpoint := if a.endpoint.hasHandle then a.endpoint else endpointClose a.endpoint }

def m770 (a : Args) : Obs := { base a with endpoint := endpointClose a.endpoint }

def m786 (a : Args) : Obs := { base a with endpoint := endpointClose a.endpoint }

def m809 (a : Args) : Obs := { base a with flags := [true] }

def m810 (a : Args) : Obs := { base a with flags := [false] }

def m836 (a : Args) : Obs := { base a with counts := let size := displaySizeModel (some a.n) (some a.m); [size.1, size.2] }

def m837 (a : Args) : Obs := { base a with counts := let size := displaySizeModel none none; [size.1, size.2] }

def m845 (a : Args) : Obs := { base a with counts := let size := displaySizeModel (some a.n) (some a.m); [size.1, size.2] }

def m847 (a : Args) : Obs := { base a with counts := let size := displaySizeModel (some a.n) (some a.m); [size.1, size.2] }

def m885 (a : Args) : Obs := { base a with counts := [allocRequestSize a.n a.m a.endpoint.throttle] }

def m893 (a : Args) : Obs := { base a with endpoint := notifyFilled a.endpoint a.bytes a.i }

def m895 (a : Args) : Obs := { base a with endpoint := notifyFilled a.endpoint a.bytes a.i }

def m905 (a : Args) : Obs := { base a with counts := [allocRequestSize a.endpoint.buffer.length a.n a.endpoint.throttle] }

def m910 (a : Args) : Obs := { base a with counts := [allocRequestSize a.endpoint.buffer.length a.n a.endpoint.throttle] }

def m938 (a : Args) : Obs := { base a with endpoint := notifyFilled a.endpoint a.bytes a.i }

def m941 (a : Args) : Obs := { base a with endpoint := notifyFilled a.endpoint a.bytes a.i }

def m992 (a : Args) : Obs := { base a with endpoint := if a.endpoint.status == .eof then { a.endpoint with status := .active } else a.endpoint }

def m1001 (a : Args) : Obs := { base a with endpoint := endpointClose a.endpoint }

def m1048 (a : Args) : Obs := { base a with pipe := freshPipe }

def m1049 (a : Args) : Obs := { base a with stream := a.pipe.readEnd }

def m1050 (a : Args) : Obs := { base a with stream := a.pipe.writeEnd }

def m1061 (a : Args) : Obs := { base a with pipe := { a.pipe with readEnd := { a.pipe.readEnd with status := .active }, writeEnd := { a.pipe.writeEnd with status := .active } } }

def m1068 (a : Args) : Obs := { base a with text := "Pipe(" ++ toString a.pipe.readEnd.buffer.length ++ ", " ++ toString a.pipe.writeEnd.buffer.length ++ ")" }

def m1076 (a : Args) : Obs := { base a with pipe := closePipeWrite a.pipe }

def m1080 (a : Args) : Obs := { base a with endpoint := { a.endpoint with hasHandle := a.flag, status := .opened } }

def m1093 (a : Args) : Obs := { base a with pipe := { readEnd := { a.pipe.readEnd with status := .active }, writeEnd := { a.pipe.writeEnd with status := .active } } }

def m1111 (a : Args) : Obs := { base a with pipe := { readEnd := { a.pipe.readEnd with status := .active }, writeEnd := { a.pipe.writeEnd with status := .active } } }

def m1128 (a : Args) : Obs := { base a with flags := [a.flag] }

def m1138 (a : Args) : Obs := { base a with endpoint := startReadingState a.endpoint }

def m1168 (a : Args) : Obs := { base a with endpoint := stopReadingState a.endpoint }

def m1178 (a : Args) : Obs := { base a with endpoint := stopReadingState a.endpoint }

def m1190 (a : Args) : Obs := let read := readbytesModel a.stream.buffer a.n; { base a with counts := [read.1], bytes := read.2.1, stream := { a.stream with buffer := read.2.2 } }

def m1191 (a : Args) : Obs := let read := readbytesModel a.stream.buffer a.n; { base a with counts := [read.1], bytes := read.2.1, stream := { a.stream with buffer := read.2.2 } }

def m1198 (a : Args) : Obs := withEndpoint a (waitReadState a.endpoint a.n)

def m1232 (a : Args) : Obs := withRead a (readAvailable a.stream)

def m1240 (a : Args) : Obs := withRead a (unsafeRead a.stream a.n)

def m1247 (a : Args) : Obs := withEndpoint a (waitReadState a.endpoint a.n)

def m1277 (a : Args) : Obs := withRead a (unsafeRead a.stream 1)

def m1292 (a : Args) : Obs := withRead a (readAvailable a.stream)

def m1302 (a : Args) : Obs := withRead a (readUntil a.stream a.byte a.flag)

def m1347 (a : Args) : Obs := { base a with counts := writeChunks a.bytes.length (max 1 a.n) }

def m1360 (a : Args) : Obs := { base a with counts := writeChunks a.n (max 1 a.m), req := completeReq a.req a.i a.j.toNat }

def m1478 (a : Args) : Obs := reqFinishObs a a.flag a.flag2 a.flag3

def m1558 (a : Args) : Obs := { base a with req := completeReq a.req a.i a.n }

def m1576 (a : Args) : Obs := reqFinishObs a a.flag a.flag2 a.flag3

def m1604 (a : Args) : Obs := { base a with counts := writeChunks a.n (max 1 a.m) }

def m1611 (a : Args) : Obs := { base a with counts := writeChunks a.n (max 1 a.m) }

def m1634 (a : Args) : Obs := { base a with counts := writeChunks a.n (max 1 a.m) }

def m1669 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m1679 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))

def m1691 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m1699 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))

def m1710 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m1720 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes (min a.n a.bytes.length))

def m1736 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.n)

def m1741 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.n)

def m1778 (a : Args) : Obs := { base a with bytes := requeueUnwritten a.bytes a.queued a.n }

def m1795 (a : Args) : Obs := { base a with bytes := a.endpoint.sendBuffer.getD [], endpoint := { a.endpoint with sendBuffer := none } }

def m1826 (a : Args) : Obs := { base a with endpoint := { a.endpoint with sendBuffer := some [] }, counts := [a.n] }

def m1836 (a : Args) : Obs := withStream a (unsafeWrite a.stream [a.byte] 1)

def m1856 (a : Args) : Obs := { base a with req := completeReq a.req a.i a.n }

def m1909 (a : Args) : Obs := { base a with req := completeReq a.req a.i 0 }

def m1916 (a : Args) : Obs := { base a with integer := a.i }

def m1917 (a : Args) : Obs := { base a with integer := a.i }

def m1919 (a : Args) : Obs := { base a with flags := [a.endpoint.hasHandle], integer := a.i }

def m1938 (a : Args) : Obs := { base a with integer := a.i, flags := [a.flag] }

def m1949 (a : Args) : Obs := { base a with integer := a.i, flags := [a.flag] }

def m1957 (a : Args) : Obs := { base a with integer := a.i, flags := [a.flag] }

def m1963 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m1969 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .devnull } }

def m1978 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m1984 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m1992 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m1995 (a : Args) : Obs := { base a with counts := [1] }

def m1996 (a : Args) : Obs := { base a with counts := [a.n] }

def m1997 (a : Args) : Obs := match pipeGetindex (a.pipe.readEnd, a.pipe.writeEnd) a.i with
      | some stream => { base a with stream }
      | none => { base a with error := some .argumentError }

def m2052 (a : Args) : Obs := { base a with redirect := redirectStdio a.redirect .keep .keep .keep }

def m2110 (a : Args) : Obs := { base a with redirect := redirectStdio a.redirect (if a.flag then .stream else .keep) (if a.flag2 then .stream else .keep) (if a.flag3 then .stream else .keep) }

def m2112 (a : Args) : Obs := { base a with redirect := a.redirect }

def m2115 (a : Args) : Obs := { base a with text := a.text }

def m2118 (a : Args) : Obs := { base a with redirect := { a.redirect with outStream := .stream } }

def m2122 (a : Args) : Obs := { base a with flags := [false] }

def m2123 (a : Args) : Obs := { base a with flags := [samePath a.text a.text2] }

def m2156 (a : Args) : Obs := { base a with redirect := redirectStdio a.redirect .keep .stream .keep }

def m2194 (a : Args) : Obs := { base a with counts := [a.n] }

def m2195 (a : Args) : Obs := { base a with counts := [a.n] }

def m2196 (a : Args) : Obs := { base a with counts := [a.n] }

def m2197 (a : Args) : Obs := { base a with flags := [a.flag] }

def m2199 (a : Args) : Obs := match peekModel a.endpoint.buffer a.n with
      | .ok bytes => { base a with bytes }
      | .error e => { base a with error := some e }

def m2216 (a : Args) : Obs := { base a with stream := freshStream .bufferStream }

def m2219 (a : Args) : Obs := { base a with flags := [isOpen a.stream] }

def m2225 (a : Args) : Obs := { base a with stream := { a.stream with writable := false } }

def m2231 (a : Args) : Obs := { base a with stream := bufferClose a.stream }

def m2238 (a : Args) : Obs := { base a with stream := bufferClose a.stream }

def m2239 (a : Args) : Obs := { base a with flags := [a.flag] }

def m2241 (a : Args) : Obs := match bufferReadByte a.stream with
      | .ok (byte, stream) => { base a with stream, bytes := [byte] }
      | .error e => { base a with error := some e }

def m2249 (a : Args) : Obs := withRead a (unsafeRead a.stream a.n)

def m2257 (a : Args) : Obs := { base a with counts := [a.stream.buffer.length] }

def m2259 (a : Args) : Obs := { base a with flags := [bufferReadable a.stream] }

def m2260 (a : Args) : Obs := { base a with flags := [bufferWritable a.stream] }

def m2262 (a : Args) : Obs := { base a with flags := [a.n ≤ a.stream.buffer.length || !isOpen a.stream] }

def m2277 (a : Args) : Obs := withRead a (readAvailable a.stream)

def m2288 (a : Args) : Obs := withRead a (readAvailable a.stream)

def m2297 (a : Args) : Obs := let read := bufferReadN a.stream a.n; { base a with bytes := read.1, stream := read.2, counts := [read.1.length] }

def m2303 (a : Args) : Obs := { base a with flags := [a.n ≤ a.stream.buffer.length || !isOpen a.stream] }

def m2337 (a : Args) : Obs := { base a with text := "BufferStream(" ++ toString a.stream.buffer.length ++ " bytes waiting)" }

def m2339 (a : Args) : Obs := withRead a (readUntil a.stream a.byte a.flag)

def m2358 (a : Args) : Obs := { base a with flags := [!isOpen a.stream] }

def m2373 (a : Args) : Obs := base a

def m2374 (a : Args) : Obs := base a

def m2376 (a : Args) : Obs := withStream a (unsafeWrite a.stream [a.byte] 1)

def m2382 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m2388 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m2395 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.bytes.length)

def m2404 (a : Args) : Obs := withStream a (unsafeWrite a.stream a.bytes a.n)

def m2416 (a : Args) : Obs := { base a with flags := [bufferEof a.stream] }

def m2427 (a : Args) : Obs := { base a with counts := [a.n] }

def m2428 (a : Args) : Obs := { base a with stream := bufferFlush a.stream }

def m2438 (a : Args) : Obs := { base a with stream := bufferSkip a.stream a.n }

def m2440 (a : Args) : Obs := { base a with stream := bufferResetEof a.stream }

/-- Dispatch by the source line of the modelled method. -/
def run : Nat → Args → Obs
  | 29, a => m29 a
  | 58, a => m58 a
  | 102, a => m102 a
  | 104, a => m104 a
  | 139, a => m139 a
  | 179, a => m179 a
  | 194, a => m194 a
  | 204, a => m204 a
  | 224, a => m224 a
  | 244, a => m244 a
  | 258, a => m258 a
  | 261, a => m261 a
  | 268, a => m268 a
  | 275, a => m275 a
  | 281, a => m281 a
  | 282, a => m282 a
  | 284, a => m284 a
  | 285, a => m285 a
  | 286, a => m286 a
  | 288, a => m288 a
  | 328, a => m328 a
  | 364, a => m364 a
  | 377, a => m377 a
  | 384, a => m384 a
  | 390, a => m390 a
  | 493, a => m493 a
  | 502, a => m502 a
  | 511, a => m511 a
  | 530, a => m530 a
  | 534, a => m534 a
  | 540, a => m540 a
  | 553, a => m553 a
  | 575, a => m575 a
  | 615, a => m615 a
  | 626, a => m626 a
  | 650, a => m650 a
  | 700, a => m700 a
  | 719, a => m719 a
  | 750, a => m750 a
  | 770, a => m770 a
  | 786, a => m786 a
  | 809, a => m809 a
  | 810, a => m810 a
  | 836, a => m836 a
  | 837, a => m837 a
  | 845, a => m845 a
  | 847, a => m847 a
  | 885, a => m885 a
  | 893, a => m893 a
  | 895, a => m895 a
  | 905, a => m905 a
  | 910, a => m910 a
  | 938, a => m938 a
  | 941, a => m941 a
  | 992, a => m992 a
  | 1001, a => m1001 a
  | 1048, a => m1048 a
  | 1049, a => m1049 a
  | 1050, a => m1050 a
  | 1061, a => m1061 a
  | 1068, a => m1068 a
  | 1076, a => m1076 a
  | 1080, a => m1080 a
  | 1093, a => m1093 a
  | 1111, a => m1111 a
  | 1128, a => m1128 a
  | 1138, a => m1138 a
  | 1168, a => m1168 a
  | 1178, a => m1178 a
  | 1190, a => m1190 a
  | 1191, a => m1191 a
  | 1198, a => m1198 a
  | 1232, a => m1232 a
  | 1240, a => m1240 a
  | 1247, a => m1247 a
  | 1277, a => m1277 a
  | 1292, a => m1292 a
  | 1302, a => m1302 a
  | 1347, a => m1347 a
  | 1360, a => m1360 a
  | 1478, a => m1478 a
  | 1558, a => m1558 a
  | 1576, a => m1576 a
  | 1604, a => m1604 a
  | 1611, a => m1611 a
  | 1634, a => m1634 a
  | 1669, a => m1669 a
  | 1679, a => m1679 a
  | 1691, a => m1691 a
  | 1699, a => m1699 a
  | 1710, a => m1710 a
  | 1720, a => m1720 a
  | 1736, a => m1736 a
  | 1741, a => m1741 a
  | 1778, a => m1778 a
  | 1795, a => m1795 a
  | 1826, a => m1826 a
  | 1836, a => m1836 a
  | 1856, a => m1856 a
  | 1909, a => m1909 a
  | 1916, a => m1916 a
  | 1917, a => m1917 a
  | 1919, a => m1919 a
  | 1938, a => m1938 a
  | 1949, a => m1949 a
  | 1957, a => m1957 a
  | 1963, a => m1963 a
  | 1969, a => m1969 a
  | 1978, a => m1978 a
  | 1984, a => m1984 a
  | 1992, a => m1992 a
  | 1995, a => m1995 a
  | 1996, a => m1996 a
  | 1997, a => m1997 a
  | 2052, a => m2052 a
  | 2110, a => m2110 a
  | 2112, a => m2112 a
  | 2115, a => m2115 a
  | 2118, a => m2118 a
  | 2122, a => m2122 a
  | 2123, a => m2123 a
  | 2156, a => m2156 a
  | 2194, a => m2194 a
  | 2195, a => m2195 a
  | 2196, a => m2196 a
  | 2197, a => m2197 a
  | 2199, a => m2199 a
  | 2216, a => m2216 a
  | 2219, a => m2219 a
  | 2225, a => m2225 a
  | 2231, a => m2231 a
  | 2238, a => m2238 a
  | 2239, a => m2239 a
  | 2241, a => m2241 a
  | 2249, a => m2249 a
  | 2257, a => m2257 a
  | 2259, a => m2259 a
  | 2260, a => m2260 a
  | 2262, a => m2262 a
  | 2277, a => m2277 a
  | 2288, a => m2288 a
  | 2297, a => m2297 a
  | 2303, a => m2303 a
  | 2337, a => m2337 a
  | 2339, a => m2339 a
  | 2358, a => m2358 a
  | 2373, a => m2373 a
  | 2374, a => m2374 a
  | 2376, a => m2376 a
  | 2382, a => m2382 a
  | 2388, a => m2388 a
  | 2395, a => m2395 a
  | 2404, a => m2404 a
  | 2416, a => m2416 a
  | 2427, a => m2427 a
  | 2428, a => m2428 a
  | 2438, a => m2438 a
  | 2440, a => m2440 a
  | _, a => base a

end JuliaLean.Streams.Methods.Stream
